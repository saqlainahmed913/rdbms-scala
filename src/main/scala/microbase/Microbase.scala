package microbase

import org.apache.spark.sql.catalyst.InternalRow
import org.apache.spark.sql.catalyst.AliasIdentifier
import org.apache.spark.sql.catalyst.analysis.TypeCheckResult.{TypeCheckFailure, TypeCheckSuccess}
import org.apache.spark.sql.execution.SparkSqlParser
import org.apache.spark.sql.catalyst.plans.logical._
import org.apache.spark.sql.catalyst.plans.NaturalJoin
import org.apache.spark.sql.catalyst.expressions._
import org.apache.spark.sql.catalyst.analysis._
import org.apache.spark.sql.catalyst.expressions.aggregate.{AggregateFunction, Average, Count, DeclarativeAggregate, Max, Sum}
import org.apache.spark.sql.catalyst.expressions.codegen.{CodegenContext, ExprCode}
import org.apache.spark.sql.catalyst.plans.JoinType
import org.apache.spark.sql.types._
import org.apache.spark.unsafe.types.UTF8String

import java.time._
import scala.collection.immutable.SortedMap
import scala.collection.mutable
import scala.io._
import scala.util.control.Breaks.break

/* All methods in this project have been used from Catalyzer scala doc provided
UBIT: sahmed34
*/

object Microbase {

  var hm: mutable.Map[Seq[String], (Seq[AttributeReference], Option[String])] = mutable.Map[Seq[String],(Seq[AttributeReference], Option[String])]()
  var hashData: mutable.HashMap[Seq[String], IndexedSeq[InternalRow]] = mutable.HashMap[Seq[String], IndexedSeq[InternalRow]]()
  //var dTypes: Seq[DataType]=Seq()
  //var sortData: mutable.SortedMap[InternalRow, IndexedSeq[InternalRow]] = mutable.SortedMap[InternalRow, IndexedSeq[InternalRow]]()(InterpretedOrdering.forSchema(dTypes))
  var primaryAtt: mutable.HashMap[Seq[String], Seq[Attribute]] = mutable.HashMap[Seq[String], Seq[Attribute]]()
  var hashAtt: mutable.HashMap[Seq[String], Seq[Attribute]] = mutable.HashMap[Seq[String], Seq[Attribute]]()
  var treeAtt: mutable.HashMap[Seq[String], Seq[Attribute]] = mutable.HashMap[Seq[String], Seq[Attribute]]()
  var hashIndex: mutable.HashMap[Any, Seq[InternalRow]] = mutable.HashMap[Any, Seq[InternalRow]]()
  var treeIndex: mutable.HashMap[Attribute, mutable.TreeMap[InternalRow,Seq[InternalRow]]] = mutable.HashMap[Attribute, mutable.TreeMap[InternalRow,Seq[InternalRow]]]()
  val parser= new SparkSqlParser()
  var number:Int=0
  var query:Int=0
  var version:Int=1

  def parseSql(sql: String): LogicalPlan = {
    parser.parsePlan(sql)
  }

  case class MyTable(name: Seq[String])
    extends LeafNode
  {
    def location: String =hm(name)._2.get
    def output: Seq[Attribute] =hm(name)._1
    /*override def maxRows:Option[Long]={ var it=tableIteration(MyTable(name))
      var count:Long=0
      while (it.hasNext){
        count=count+1
        it.next
      }
      Some(count)
    }*/
    def tableData:IndexedSeq[InternalRow]=hashData(name)
    def it:Iterator[InternalRow]=tableData.iterator
    def tableHashIndex:Seq[Attribute]=if(hashAtt.contains(name)){
      hashAtt(name)
    }else{
      Seq()
    }
    def tableTreeIndex:Seq[Attribute]=if(treeAtt.contains(name)){
      treeAtt(name)
    } else {
      Seq()
    }
  }

  case class SubQueryResult(name: Seq[String],plan: LogicalPlan) extends LeafNode{
    def output: Seq[Attribute] =hm(name)._1
  }

  def resolveProjectFilter(analyzedplan: LogicalPlan): LogicalPlan={
    analyzedplan.transformUp{
      case GlobalLimit(limitExpr,child)=>child
      case Sort(order,global,child)=>Sort(sortOrderResolver(order,child),global,child)
      case Aggregate(groupingExpressions,aggregateExpressions,child)=>aggregateResolver(groupingExpressions,aggregateExpressions,child)
      case Project(projectList,child)=>Project(projectlistResolver(projectList,child),child)
      case Filter(expression,child)=>Filter(expressionResolver(expression,child),child)
      case Join(left,right,joinType,condition,joinHint)=>resolveJoin(left,right,resolveJointype(joinType),resolveJoinCondition(left,right,joinType,condition),joinHint)
      case SubqueryAlias(identifier,child)=>resolveAlias(identifier,child)
      case UnresolvedRelation(nameElements, _, _) => MyTable(nameElements)
    }
  }
  def aggregateResolver(groupExp: Seq[Expression], selectExp: Seq[NamedExpression], plan: LogicalPlan):LogicalPlan={
    var newSelectExp:Seq[NamedExpression]=projectlistResolver(selectExp,plan)
    val newExp:Seq[Expression]=groupExp.flatMap(f=> Seq(expressionResolver(f,plan)))
    Aggregate(newExp,newSelectExp,plan)
  }
  def sortOrderResolver(order: Seq[SortOrder], child: LogicalPlan): Seq[SortOrder]={
    order.flatMap(s=>Seq(new SortOrder(expressionResolver(s.child,child),s.direction,s.nullOrdering,s.sameOrderExpressions)))
  }

  def resolveAlias(identifier: AliasIdentifier, plan: LogicalPlan): LogicalPlan ={
    var seqattr: Seq[AttributeReference]=Seq()
    var newLp: LogicalPlan=null
    for (f <- plan.output) {
      val id = NamedExpression.newExprId
      seqattr = seqattr ++ Seq(AttributeReference(f.name, f.dataType)(id,Seq(identifier.name)))
    }
    /*var last:LogicalPlan=null
    for(f<-plan) {
      last=f
    }*/

      plan match {
        case u: MyTable =>
          if(!hm.contains(Seq(identifier.name))) {
            hm += (Seq(identifier.name) -> (seqattr, Option(u.location)))
            hashData += (Seq(identifier.name) -> u.tableData)
          }
          newLp=MyTable(Seq(identifier.name))
        //case u: Project=> hm += (Seq(identifier.name) -> (seqattr, Option(u.child match{case v:MyTable=>v.location})))
        case _=> hm += (Seq(identifier.name) -> (seqattr, Option("")))
          newLp=SubQueryResult(Seq(identifier.name),plan)
      }
    newLp
  }
  def resolveJoin(left: LogicalPlan, right: LogicalPlan, joinType: JoinType, maybeExpression: Option[Expression], hint: JoinHint):LogicalPlan={
    //println(left.maxRows.get+" "+ right.maxRows.get)
    /*if(maybeExpression.isDefined) {
      if (left.maxRows.get >= right.maxRows.get) {
        Join(left, right, joinType, maybeExpression, hint)
      } else {
        Join(right, left, joinType, maybeExpression, hint)
      }
    }
    else
    {*/
    if(left.fastEquals(right)) {
      var tableName=right match {
        case u: MyTable => u.name.head
      }
      var newAlias:AliasIdentifier=new AliasIdentifier(tableName+(version+1).toString)
      Join(left, resolveAlias(newAlias,right), joinType, maybeExpression, hint)
    }
    else{
      Join(left, right, joinType, maybeExpression, hint)
    }
    //}
  }

  def resolveJointype(joinType: JoinType) :JoinType={
    val newJoin=joinType match{
      case NaturalJoin(tpe)=>tpe
      case _=>joinType
    }
    newJoin
  }

  def resolveJoinCondition(plan: LogicalPlan, plan1: LogicalPlan,joinType: JoinType,condition: Option[Expression]): Option[Expression]={
    val newSeq: Seq[NamedExpression]=plan.output ++ plan1.output
    if(condition.isEmpty) {
      return None
    }
    val tempExpr: Expression=condition.get.transform {
      case UnresolvedAttribute(nameParts) => if(nameParts.length==1){
        newSeq.filter(d => nameParts.head.toUpperCase.contains(d.name)).head
      }else{
        newSeq.filter(d=> Seq(nameParts.head).equals(d.qualifier) && nameParts(1).toUpperCase.contains(d.name)).head
      }
    }
    val maybeExpr: Option[Expression]=Some(tempExpr)
      maybeExpr
  }

  def expressionResolver(expression: Expression,child: LogicalPlan): Expression ={
    val newSeq: Seq[NamedExpression]=child.output
      val newExpr=expression.transformUp {
        case UnresolvedAttribute(nameParts) => if(nameParts.length==1){
          newSeq.filter(d => nameParts.head.toUpperCase.contains(d.name)).head
        }else{
          newSeq.filter(d=> Seq(nameParts.head).equals(d.qualifier) && nameParts(1).toUpperCase.contains(d.name)).head
        }
        /*case LessThan(left,right)=>var flag=0
          flag=right match {
          case Cast(Literal(value, dataType),dType,timeZoneId) => dataType match {
            case u: DecimalType => if (u.scale > 8) {
              flag+1
            } else {
              flag
            }
            case _=>flag
          }
          case _=>flag
        }
          if(flag>0){
            LessThanOrEqual(left,right)
          }else{
            LessThan(left,right)
          }*/
        case UnresolvedFunction(name,arguments,isDistinct,filter,ignoreNulls)=>
          val builder =
            FunctionRegistry.builtin
              .lookupFunctionBuilder(name)
              .getOrElse {
                throw new RuntimeException(
                  s"Unable to resolve function `${name}`"
                )
              }
          builder(arguments)
      }

    /*val resolveExp=newExpr.transformUp{
      case Multiply(left,Cast(child,FloatType,_),_)=>Multiply(Cast(left,FloatType),Cast(child,FloatType))
    }*/
    newExpr
    //resolveExp
  }

  def projectlistResolver(projectlist: Seq[NamedExpression],child: LogicalPlan): Seq[NamedExpression]={
    val newSeq: Seq[NamedExpression]=child.output
    //println(newSeq)
    var newlist: Seq[NamedExpression]=Seq()
    for (f <- projectlist) {
      newlist=f match {
        case u: UnresolvedAttribute => if (u.nameParts.length == 1) {
          newlist ++ newSeq.filter(d => f.name.toUpperCase == d.name)
        }
        else {
          newlist ++ MyTable(Seq(u.nameParts.head)).output.filter(d => u.nameParts(1).toUpperCase == d.name)
        }
        case u: UnresolvedStar => if (u.target.isEmpty) {
          newlist ++ newSeq
        } else {
          newlist ++ MyTable(u.target.get).output
        }
        case u:UnresolvedAlias=>
          val newExp=Seq(Alias(expressionResolver(u.child,child),"")())
          newlist ++ newExp
        // newlist ++ Seq(Alias(expressionResolver(u.child,child),"")())
        case u:Alias =>
          newlist ++ Seq(Alias(expressionResolver(u.child,child),u.name.toUpperCase)(u.exprId,child.output.head.qualifier))
          //child.output ++ Seq(AttributeReference(u.name,u.child.dataType)(u.exprId,child.output.head.qualifier))

      }
    }
    newlist
  }

  def compareFunc(a: InternalRow, b: InternalRow, order: Seq[SortOrder], BRefSeq: Seq[BoundReference]): Boolean= {
    SortHelper(a,b,BRefSeq) match {
      case 0 => if (order.tail.nonEmpty) {
        compareFunc(a, b, order.tail, BRefSeq.tail)
      } else {
        false
      }
      case 1 => order.head.direction match {
        case Ascending => false
        case Descending => true
      }
      case -1 => order.head.direction match {
        case Ascending => true
        case Descending => false
      }
    }
  }
  def SortHelper(a: InternalRow,b: InternalRow,BRefSeq:Seq[BoundReference]): Int={
    val boundRef=BRefSeq.head
    val compareResult:Int= boundRef.dataType match {
      case IntegerType => a.getInt(boundRef.ordinal).compare(b.getInt(boundRef.ordinal))
      case FloatType => a.getFloat(boundRef.ordinal).compare(b.getFloat(boundRef.ordinal))
      case DoubleType => a.getDouble(boundRef.ordinal).compare(b.getDouble(boundRef.ordinal))
      case DateType => a.getInt(boundRef.ordinal).compare(b.getInt(boundRef.ordinal))
      case StringType => if(a.getString(boundRef.ordinal).compare(b.getString(boundRef.ordinal))>0){
        1
      }else if(a.getString(boundRef.ordinal).compare(b.getString(boundRef.ordinal))<0){
        -1
      }else{
        0
      }
    }
    compareResult
  }
  def evalSort(order: Seq[SortOrder],child: LogicalPlan,it: Iterator[InternalRow]): Iterator[InternalRow]= {
    val newSeq: IndexedSeq[InternalRow] = it.toIndexedSeq
    var BRefSeq:Seq[BoundReference]=Seq()
    for(f<-order){
      BRefSeq=BRefSeq ++ Seq(Bref(f.child, child.output).head)
    }
    newSeq.sortWith((a,b)=>compareFunc(a,b,order,BRefSeq)).iterator
  }

  def evalUnion(children: Seq[LogicalPlan],byName: Boolean,allowMissingCol: Boolean): Iterator[InternalRow] ={
    var newIterator:Iterator[InternalRow]=Iterator()
    for(f<-children){
      newIterator=newIterator ++ eval(f)
    }
    newIterator
  }
  def evalLocalLimit(expression: Expression, it: Iterator[InternalRow]):Iterator[InternalRow]={
    val limit: Int=expression match{
      case u:Literal=>u.value.asInstanceOf[Int]
    }
    it.slice(0,limit)
  }

  def getAggregate(aggregateExpressions: Seq[NamedExpression],groupingExpressions: Seq[Expression],child: LogicalPlan):Seq[Seq[Expression]]={
    var agg:Seq[Expression]=Seq()
    var aggBufferFields:Seq[AttributeReference]=Seq()
    var newInitialValues:Seq[Expression]=Seq()
    var newUpdate:Seq[Expression]=Seq()
    var groupExp:Seq[Attribute]= Seq()
      groupingExpressions.map{exp=>groupExp=groupExp++exp.references.toSeq}
    var newagg:Seq[Expression]=Seq()
    aggregateExpressions.map {
      case u:Attribute=>agg=agg ++ Seq(u)
      case Alias(child, name) => child match {
        case u: AggregateFunction =>
          agg=agg++ Seq(u)
          aggBufferFields=aggBufferFields ++ u.aggBufferAttributes
      }
    }
    for(field<-agg) {
      field match{
        case u:Attribute=>newagg=newagg++Bref(u,aggBufferFields++groupExp)
        case u:DeclarativeAggregate=>
          for(f<-u.initialValues){
            newInitialValues=newInitialValues ++
              Seq(f)
          }
        for(f<-u.updateExpressions){
          newUpdate=newUpdate++
            Seq(f.transform{
              case u:AttributeReference=>Bref(u,aggBufferFields++child.output).head
            })
        }
          var newExp=u.evaluateExpression
          newagg=newagg++
            Seq(newExp.transform{
              case u:AttributeReference=>Bref(u,aggBufferFields).head
            })
      }

    }
    Seq(newInitialValues)++Seq(newUpdate)++Seq(newagg)
  }
  def evalAgg(aggregateExpressions: Seq[NamedExpression],child: LogicalPlan,it: Iterator[InternalRow]):Iterator[InternalRow]= {
    var rows = it.toIndexedSeq
    //println(rows)
    var newSeq: Seq[Any] = Seq()
    var newAgg:Seq[Expression]=Seq()
    for (f <- aggregateExpressions) {
      newAgg = newAgg ++ Seq(f.transformUp {
        case u: Attribute => Bref(u, child.output).head
      })
    }
    for (f <- newAgg) {
      f match {
        case u: Alias => u.child match {
          case v: Count => newSeq = newSeq ++ Seq(rows.foldLeft(0L)((accum, row) => accum + 1))
          case v: Sum => v.child.dataType match {
            case IntegerType=>newSeq = newSeq ++ Seq (rows.foldLeft (0L) ((accum, row) => accum + v.child.eval(row).asInstanceOf[Int] ) )
            case _=>newSeq = newSeq ++ Seq (rows.foldLeft (0.0) ((accum, row) => accum + Cast(v.child,DoubleType).eval(row).asInstanceOf[Double] ) )
          }
          case v:Average=>v.child.dataType match {
            case IntegerType=>newSeq = newSeq ++ Seq (rows.foldLeft (0L) ((accum, row) => accum + v.child.eval(row).asInstanceOf[Int] )/rows.foldLeft(0L)((accum, row) => accum + 1) )
            case _=>newSeq = newSeq ++ Seq (rows.foldLeft (0.0) ((accum, row) => accum + Cast(v.child,DoubleType).eval(row).asInstanceOf[Double] )/rows.foldLeft(0L)((accum, row) => accum + 1) )
          }
        }
      }
    }
    Iterator(InternalRow.fromSeq(newSeq))
  }
  def evalAggGroup(groupingExpressions: Seq[Expression], aggregateExpressions: Seq[NamedExpression],child: LogicalPlan, it: Iterator[InternalRow]):Iterator[InternalRow]= {
    var rows = it.toIndexedSeq
    //println(rows)
    var newSeq: Seq[Any] = Seq()
    var newAgg:Seq[Expression]=Seq()
    for (f <- groupingExpressions) {
      newAgg = newAgg ++ Seq(f.transformUp {
        case u: Attribute => Bref(u, child.output).head
      })
    }
    var aggMap=rows.groupBy{row=>var key:Seq[Any]=Seq()
      for(f <- newAgg){
        key=key ++ Seq(f.eval(row))
      }
      InternalRow.fromSeq(key)
    }
    //println(aggMap)
    newAgg=Seq()
    for (f <- aggregateExpressions) {
      newAgg = newAgg ++ Seq(f.transformUp {
        case u: Attribute => Bref(u, child.output).head
      })
    }
    var newIt:IndexedSeq[InternalRow]=IndexedSeq()
    for (g <-aggMap.keys ) {
      var newRows=aggMap(g)
      newSeq=Seq()
      for(f <- newAgg) {
        f match {
          case u: Alias => u.child match {
            case v: Count => newSeq = newSeq ++ Seq(newRows.foldLeft(0L)((accum, row) => accum + 1))
            case v: Sum => v.child.dataType match {
              case IntegerType => newSeq = newSeq ++ Seq(newRows.foldLeft(0L)((accum, row) => accum + v.child.eval(row).asInstanceOf[Int]))
              case _ => newSeq = newSeq ++ Seq(newRows.foldLeft(0.0)((accum, row) => accum + Cast(v.child, DoubleType).eval(row).asInstanceOf[Double]))
            }
            case v: Average => v.child.dataType match {
              case IntegerType => newSeq = newSeq ++ Seq(newRows.foldLeft(0L)((accum, row) => accum + v.child.eval(row).asInstanceOf[Int]) / newRows.foldLeft(0L)((accum, row) => accum + 1))
              case _ => newSeq = newSeq ++ Seq(newRows.foldLeft(0.0)((accum, row) => accum + Cast(v.child, DoubleType).eval(row).asInstanceOf[Double]) / newRows.foldLeft(0L)((accum, row) => accum + 1))
            }
          }
          case u: BoundReference => newSeq=newSeq ++ Seq(u.eval(newRows(0)))
        }
      }
      newIt= newIt ++ Seq(InternalRow.fromSeq(newSeq))
    }
    newIt.iterator
  }
  def evalAggregate(groupingExpressions: Seq[Expression], aggregateExpressions: Seq[NamedExpression],child: LogicalPlan, TIterator: Iterator[InternalRow]):Iterator[InternalRow]= {
    //val t1=System.nanoTime()
    if (TIterator.isEmpty) {
      Iterator()
    } else {
      val t1=System.nanoTime()
      var groupBuffer: Seq[InternalRow] = Seq()
      var aggBuffer: InternalRow = null
      var resultBuffer: Seq[InternalRow] = Seq()
      var resultSeq: Seq[Any] = Seq()
      val aggExp: Seq[Seq[Expression]] = getAggregate(aggregateExpressions, groupingExpressions, child)
      val init: Seq[Expression] = aggExp.head
      val Upd: Seq[Expression] = aggExp(1)
      //val evalExp: Seq[Expression] = aggExp(2)
      val newExp: Seq[Expression] = aggExp(2)
      //println(newExp)
      var newSeq: Seq[Any] = Seq()
      var hash: mutable.HashMap[InternalRow, InternalRow] = mutable.HashMap[InternalRow, InternalRow]()
      var key: InternalRow = null
      var count = 0
      for (f <- init) {
        newSeq = newSeq ++ Seq(f.eval())
      }
      var initAggBuffer: InternalRow = InternalRow.fromSeq(newSeq)
      while (TIterator.hasNext) {
        val Irow = TIterator.next
        var Irowseq: Seq[Any] = Seq()
        if (groupingExpressions.nonEmpty) {
          for (f <- groupingExpressions) {
            f match {
              case u: Attribute => val b: BoundReference = Bref(f, child.output).head
                val newExp = Rowlookup(b.ordinal, f)
                Irowseq = Irowseq ++ Seq(newExp.eval(Irow))
            }
          }
          key = InternalRow.fromSeq(Irowseq)
          if (!hash.contains(key)) {
            groupBuffer = groupBuffer ++ Seq(key)
            hash += (key -> initAggBuffer)
          }
          aggBuffer = hash(key)
        } else {
          if (count == 0) {
            count = count + 1
            aggBuffer = initAggBuffer
          }
        }
        newSeq = Seq()
        for (f <- Upd) {
          newSeq = newSeq ++ Seq(f.eval(new JoinedRow(aggBuffer, Irow)))
        }
        aggBuffer = InternalRow.fromSeq(newSeq)
        if (groupingExpressions.nonEmpty) {
          hash += (key -> aggBuffer)
        }
      }
      //EvaluateExp
      if (groupingExpressions.nonEmpty) {
        for (f <- groupBuffer) {
          resultSeq = Seq()
          for (g <- newExp) {
            resultSeq = resultSeq ++ Seq(g.eval(new JoinedRow(hash(f), f)))
          }
          resultBuffer = resultBuffer ++ Seq(InternalRow.fromSeq(resultSeq))
        }
      } else {
        /*if (aggBuffer.anyNull) {
        resultBuffer = Seq()
      }
      else {*/
        for (g <- newExp) {
          resultSeq = resultSeq ++ Seq(g.eval(aggBuffer))
        }
        resultBuffer = resultBuffer ++ Seq(InternalRow.fromSeq(resultSeq))
        //}
      }
      //println(resultBuffer)
      //val t2=System.nanoTime()
      //println("Aggregate Time"+(t2-t1)/math.pow(10,9))
      resultBuffer.iterator
      //Iterator(resultBuffer)
    }
  }
  def evalProject(target: Seq[Expression],child: LogicalPlan,TIterator: Iterator[InternalRow]):Iterator[InternalRow]={
    val projIterator=TIterator
    //println(target+" "+child.output)
    var NewRow:Iterator[InternalRow]=Iterator()
    while(projIterator.hasNext){
      val Irow=projIterator.next
      var IrowSeq:Seq[Any]=Seq()
      for(f<-target) {
        f match {
          case u:Attribute =>val b:BoundReference=Bref(f,child.output).head
            val newExp=Rowlookup(b.ordinal,f)
            IrowSeq=IrowSeq ++ Seq(newExp.eval(Irow))
          case u:Alias=>val newExp=u.child.transformUp{
            //case Multiply(left,Literal(value,FloatType),_)=>Literal(left.eval(Irow).asInstanceOf[Float]*value.asInstanceOf[Float])
            case u:Attribute=>Bref(u,child.output).head
          }
            IrowSeq=IrowSeq ++ Seq(newExp.eval(Irow))
        }
      }
      NewRow=NewRow ++ Iterator(InternalRow.fromSeq(IrowSeq))
    }
    NewRow
  }
  def getHashExp(exp:Seq[Expression],right:Expression,it: Iterator[InternalRow]):Iterator[InternalRow]={
    if(exp.isEmpty){
      it
    }else{
      hashIndex(right.eval()).iterator
    }
  }
  def evalFilterTable(exp: Expression, child: MyTable, it: Iterator[InternalRow]): Iterator[InternalRow] = {
    var c = 0
    var seqExp: Seq[Expression] = splitAnds(exp)
    var newIt: Iterator[Seq[InternalRow]] = Iterator()
    for (f <- seqExp) {
      //println(f)
      if (f.references.size == 1 && child.tableTreeIndex.contains(f.references.head) && c == 0) {
        //var newMap:mutable.Map[InternalRow,Seq[InternalRow]]=mutable.Map.empty[InternalRow,Seq[InternalRow]]
        newIt = f match {
          case u: LessThanOrEqual => treeIndex(u.left.references.head).rangeTo(InternalRow.fromSeq(Seq(u.right.eval()))).valuesIterator
          case u: LessThan => treeIndex(u.left.references.head).rangeUntil(InternalRow.fromSeq(Seq(u.right.eval()))).valuesIterator
          case u: GreaterThanOrEqual => treeIndex(u.left.references.head).rangeFrom(InternalRow.fromSeq(Seq(u.right.eval()))).valuesIterator
          case u: GreaterThan => (treeIndex(u.left.references.head).rangeFrom(InternalRow.fromSeq(Seq(u.right.eval()))) -- treeIndex(u.left.references.head)(InternalRow.fromSeq(Seq(u.right.eval())))).valuesIterator
        }
        c = c + 1
      }
    }
    var filterIt:Iterator[InternalRow]=if(newIt.nonEmpty){
      newIt.flatten
    }else{
      it
    }
    if (seqExp.length == 1 && c==1) {
        filterIt
    } else {
      val condition = exp.transformUp {
        case u: Attribute => Bref(u, child.output).head
      }
      val newIterator = filterIt.filter(row => condition.eval(row).asInstanceOf[Boolean])
      newIterator
    }
  }
  /*def evalFilterTable(expression: Expression, child: MyTable, it: Iterator[InternalRow]): Iterator[InternalRow] ={
    var filterIterator:Iterator[InternalRow]=it
    val exp:Seq[Expression]=splitAnds(expression)
    var hashExp:Seq[Expression]=Seq()
    var treeExp:Seq[Expression]=Seq()
    var rightExp:Expression=null
    var nonHashExp:Seq[Expression]=Seq()
    var newMap:mutable.SortedMap[InternalRow,Seq[InternalRow]]=mutable.SortedMap.empty[InternalRow,Seq[InternalRow]](InterpretedOrdering.forSchema(Seq(IntegerType)))
    for(f<-exp){
      if(f.references.size == 1 ){
        if(child.tableHashIndex.contains(f.references.head)) {
          f match {
            case u: EqualTo => hashExp = Seq(f)
              rightExp = u.right
            case _ => nonHashExp = nonHashExp ++ Seq(f)
          }
        } else if(child.tableTreeIndex.contains(f.references.head)){
          if(newMap.isEmpty){
            newMap=treeIndex(f.references.head)
          }
          f match {
            case u:LessThan=> newMap=newMap.rangeUntil(InternalRow.fromSeq(Seq(u.right.eval())))
            case u:LessThanOrEqual=>newMap=newMap.rangeTo(InternalRow.fromSeq(Seq(u.right.eval())))
            case u:GreaterThan=>newMap=newMap.rangeFrom(InternalRow.fromSeq(Seq(u.right.eval()))) -- treeIndex(f.references.head)(InternalRow.fromSeq(Seq(u.right.eval())))
            case u:GreaterThanOrEqual=>newMap=newMap.rangeFrom(InternalRow.fromSeq(Seq(u.right.eval())))
            case _=>  nonHashExp = nonHashExp ++ Seq(f)
          }
        }
        else{
          nonHashExp = nonHashExp ++ Seq(f)
        }
      }else{
        nonHashExp = nonHashExp ++ Seq(f)
      }
    }
    var newRow:Seq[InternalRow]=Seq()
    if(newMap.nonEmpty){
      newRow=newMap.values.toIndexedSeq.flatten
    }
    //println(newRow.length)
    //newRow.foreach(a=>println(a))
    if(newRow.nonEmpty){
      filterIterator=newRow.iterator
    }
    //println(nonHashExp)
    filterIterator=if(nonHashExp.nonEmpty){
      evalFilter(combineAnds(nonHashExp), child, getHashExp(hashExp,rightExp, filterIterator))
    } else {
      getHashExp(hashExp,rightExp, filterIterator)
    }

    /*val condition=expression.transformUp{
      case u:Attribute=>Bref(u,child.output).head
    }
    val newIterator=filterIterator.filter(row=>condition.eval(row).asInstanceOf[Boolean])
    newIterator*/
    filterIterator
  }*/

  def evalFilter(expression: Expression,child: LogicalPlan,TIteration: Iterator[InternalRow]): Iterator[InternalRow]={
    var filterIterator=TIteration
    //println(expression.references)
    /*var rows: Iterator[InternalRow] = getHashExp(expression)
    if (rows.nonEmpty) {
        filterIterator = rows
    }*/
    /*var filterIterator=child match{
      case u:MyTable=>if(u.tableHashIndex.nonEmpty){
        if(expression.references.toSeq.contains(u.tableHashIndex.head)){
        getHashExp(expression,u)
      }else{
          TIteration
        } }
      else{
        TIteration
      }
      case _=>TIteration
    }*/
    val condition=expression.transformUp{
      case u:Attribute=>Bref(u,child.output).head
    }
    val newIterator=filterIterator.filter(row=>condition.eval(row).asInstanceOf[Boolean])
    newIterator
  }

  def hashTable(it: Iterator[InternalRow], plan: LogicalPlan, expression: Expression): Map[Seq[Any], Seq[InternalRow]]={
    var hash: Map[Seq[Any], Seq[InternalRow]] = Map[Seq[Any], Seq[InternalRow]]()
    var expAtt=expression.references
    var planAtt=plan.outputSet
    var newSeq=it.toSeq
    var BindPosition:Seq[BoundReference]=Seq()
    for(f<-expAtt){
      BindPosition=BindPosition ++ Bref(f,plan.output)
    }
    //newSeq.groupBy{x=> Rowlookup(ref.ordinal,ref).eval(x)}
    newSeq.groupBy { x =>
      var key:Seq[Any]=Seq()
      for (f <- BindPosition) {
        key = key ++ Seq(Rowlookup(f.ordinal, f).eval(x))
      }
      key
    }
    //println(expAtt+" "+planAtt+" "+BindPosition)
    /*while(it.hasNext){
      var key:Seq[Any]=Seq()
      var value:Seq[InternalRow]=Seq()
      var Irow=it.next
      for(f<-BindPosition){
        key=key ++ Seq(Rowlookup(f.ordinal,f).eval(Irow))
      }
      if(hash.contains(key)){
        value=hash(key) ++ Seq(Irow)
      }
      else{
        value=value ++ Seq(Irow)
      }
      hash += (key -> value)
    }*/
    //println(hash)
    //hash
  }



  def evalJoin(leftIterator: Iterator[InternalRow], rightIterator: Iterator[InternalRow],leftTable: LogicalPlan,rightTable: LogicalPlan,joinType: JoinType, maybeExpression: Option[Expression]): Iterator[InternalRow] ={
    //InternalRow.fromSeq(leftRow.toSeq(leftTable.schema) ++ rightRow.toSeq(rightTable.schema))
    if(maybeExpression.isEmpty){
      var rightRows=rightIterator.toSeq
      leftIterator.flatMap ( leftRow =>
        rightRows.map ( rightRow =>
          new JoinedRow(leftRow, rightRow)
        )
      )
    }
    else {
        var h: Map[Seq[Any], Seq[InternalRow]] = Map[Seq[Any], Seq[InternalRow]]()
        h = hashTable(rightIterator, rightTable, maybeExpression.get)

        var expAtt = maybeExpression.get.references
        //var planAtt = leftTable.outputSet
        var BindPosition: Seq[BoundReference] = Seq()
        for (f <- expAtt) {
          BindPosition = BindPosition ++ Bref(f, leftTable.output)
        }

      var newIterator:Iterator[InternalRow]=Iterator()
      for(leftRow<-leftIterator){
        var key: Seq[Any] = Seq()
        for (f <- BindPosition) {
          key = key ++ Seq(Rowlookup(f.ordinal, f).eval(leftRow))
        }
        if(h.contains(key)){
          h(key).map(rightRow => newIterator=newIterator ++ Iterator(new JoinedRow(leftRow, rightRow)))
        }
      }
        newIterator
      }
  }
  def evalSubQuery(name: Seq[String], it: Iterator[InternalRow]): Iterator[InternalRow]={
    it
  }

  def evalMyTable(table: MyTable): Iterator[InternalRow]={
    //val TIterator=tableIteration(table)
    val TIterator:Iterator[InternalRow]=table.it
    TIterator
  }

  case class tableIteration(table: MyTable) extends Iterator[InternalRow]{
    var dTypes: Seq[DataType]=table.schema.map(f=>f.dataType)
    var open: BufferedSource=Source.fromFile(table.location)
    var current: Iterator[String]=open.getLines()
    //var data: Seq[String]=current.toIndexedSeq
    //var c:Int=0
    def hasNext: Boolean = current.hasNext
    def next: InternalRow={
      val line=current.next().split('|')
      //val line=data(c).split('|')
      var count=0
      var seqNew:Seq[Any]=Seq()
      for(i<-line){
        seqNew=seqNew ++ Seq(dTypes(count) match{
          case IntegerType=>i.toInt
          case FloatType=>i.toFloat
          case DoubleType=>i.toDouble
          case DateType=>parseDate(i)
          case StringType=>UTF8String.fromString(i)
        })
        count=count+1
      }
      //c=c+1
      val irow=InternalRow.fromSeq(seqNew)
      irow
    }
    def parseDate(str: String): Int={
      val elements = str.split('-')
      LocalDate.of(elements(0).toInt, elements(1).toInt, elements(2).toInt).toEpochDay.toInt
    }
    def close():Unit=open.close()
  }

  def eval(plan: LogicalPlan) :Iterator[InternalRow]={
    val it=plan match{
      case Union(children, byName, allowMissingCol)=>evalUnion(children,byName,allowMissingCol)
      case LocalLimit(limitExpr,child)=>evalLocalLimit(limitExpr,eval(child))
      case Sort(order,global,child)=>evalSort(order,child,eval(child))
      case Aggregate(groupingExpressions,aggregateExpressions,child)=>//evalAggregate(groupingExpressions,aggregateExpressions,child,eval(child))
      if(groupingExpressions.isEmpty){
        evalAgg(aggregateExpressions,child,eval(child))
      } else {
        evalAggGroup(groupingExpressions,aggregateExpressions,child,eval(child))
      }
      case Project(target,child)=>evalProject(target,child,eval(child))
      case Filter(condition,child)=>//evalFilter(condition,child,eval(child))
        child match{
        case u:MyTable=>evalFilterTable(condition,u,eval(u))
        case _=>evalFilter(condition,child,eval(child))
      }
      case Join(left,right,joinType,condition,joinHint)=>evalJoin(eval(left),eval(right),left,right,joinType,condition)
      case SubQueryResult(name,child)=>evalSubQuery(name,eval(child))
      case MyTable(name)=> evalMyTable(MyTable(name))
    }
    it
  }

  def Bref(expression: Expression,output: Seq[Attribute]): Seq[BoundReference]= {
    var att:Attribute=null
    var firstcol:Int=0
    var BrefSeq: Seq[BoundReference]=Seq()
    expression match{
      case u:Attribute=> att=u
    }
    for (f <- output) {
      val Bref = BoundReference(firstcol, f.dataType, f.nullable)
      if(f.exprId.equals(att.exprId)) {
        BrefSeq = BrefSeq ++ Seq(Bref)
      }
      firstcol += 1
    }
    BrefSeq
  }

  case class Rowlookup(position: Int,expr: Expression) extends Expression {
    def doGenCode(ctx: CodegenContext, ev: ExprCode): ExprCode = expr.genCode(ctx)
    def dataType: DataType = expr.dataType
    def nullable: Boolean = true
    def children: Seq[Expression] = expr.children
    def eval(row: InternalRow): Any = row.get(position,dataType)
  }

  def splitAnds(expr: Expression): Seq[Expression] = {
    expr match {
      case And(a, b) => splitAnds(a) ++ splitAnds(b)
      case _ => Seq(expr)
    }
  }

  def combineAnds(seqExp:Seq[Expression]): Expression={
    var newExp:Expression=seqExp.head
    if(seqExp.length>1){
      for (exp <- seqExp.tail) {
        newExp = And(newExp, exp)
      }
    }
    newExp
  }

  def newJoin(filterExp: Expression, left: LogicalPlan, right: LogicalPlan, joinExp: Option[Expression], joinType: JoinType,joinHint: JoinHint):LogicalPlan={
    var leftCondition:Seq[Expression]=Seq()
    var rightCondition:Seq[Expression]=Seq()
    var newJoinCondition:Seq[Expression]=Seq()
    var joinCondition:Seq[Expression]=if(joinExp.isEmpty){
      Seq()
    }else{
      splitAnds(joinExp.get)
    }
    var noneCondition:Seq[Expression]=Seq()
    var expSeq:Seq[Expression]=splitAnds(filterExp) ++ joinCondition
    for(exp<-expSeq){
      if(exp.references.subsetOf(left.outputSet)){
        leftCondition=leftCondition ++ Seq(exp)
      }
      else if(exp.references.subsetOf(right.outputSet)){
        rightCondition=rightCondition ++ Seq(exp)
      }
      else{
        exp match {
          case u:EqualTo=>
            newJoinCondition = newJoinCondition ++ Seq(exp)
          case _=>
            noneCondition=noneCondition ++ Seq(exp)
        }
      }
    }

    var newLeft=if(leftCondition.isEmpty){
      left
    }else{Filter(combineAnds(leftCondition),left)}

    var newRight=if(rightCondition.isEmpty){
      right
    }else{Filter(combineAnds(rightCondition),right)}

    var newJoinExp =if(newJoinCondition.isEmpty) {
      None
    }else {
      Some(combineAnds(newJoinCondition))
    }


    if(noneCondition.isEmpty){
      Join(newLeft,newRight,joinType,newJoinExp,joinHint)
    } else {
      Filter(combineAnds(noneCondition),Join(newLeft,newRight,joinType,newJoinExp,joinHint))
    }

  }

  trait OptimizationRule{
    def apply(plan: LogicalPlan):LogicalPlan
  }

  object PushDownSelections extends OptimizationRule{
    def apply(plan: LogicalPlan):LogicalPlan={
      plan.transformDown{
        case Filter(condition,Join(left,right,joinType,expression,joinHint))=> newJoin(condition,left,right,expression,joinType,joinHint)
        case SubQueryResult(name,plan)=>SubQueryResult(name,apply(plan))
      }
    }
  }

  val rules:Seq[OptimizationRule]=Seq(PushDownSelections)

  def onePass(plan: LogicalPlan):LogicalPlan={
    var current=plan
    for(rule<-rules){
      current=rule.apply(current)
    }
    current
  }

  def fixpoint(plan: LogicalPlan): LogicalPlan={
    var current=plan
    var last:LogicalPlan=null
    while(last==null || !current.fastEquals(last)){
      last=current
      current = onePass(current)
      //println(current)
    }
    current
  }
  def projectToAggregate(projectList: Seq[NamedExpression], plan: LogicalPlan): LogicalPlan={
    var count:Int=0
    for(f<-projectList){
      count=f match{
        case Alias(child, name) => child match{
          case u:AggregateFunction=>count+1
          case _=>count
        }
        case _=>count
      }
    }
    if(count==0){
      Project(projectList,plan)
    }else{
      Aggregate(Seq(),projectList,plan)
    }
  }
  def resolveAggregate(plan: LogicalPlan): LogicalPlan={
    plan.transformDown{
      case Project(projectList,child)=>projectToAggregate(projectList,child)
      case SubQueryResult(name,plan)=>SubQueryResult(name,resolveAggregate(plan))
    }
  }

  def parseDate(str: String): Int={
    val elements = str.split('-')
    LocalDate.of(elements(0).toInt, elements(1).toInt, elements(2).toInt).toEpochDay.toInt
  }

  def main(args: Array[String]): Unit={
    //val a: String = "SELECT bar, bar * 15 as biz, baz FROM R Order by bar asc,baz asc limit 10;"
    //val b: String = "CREATE table R (bar int, Baz int)  USING csv OPTIONS(path 'data/R.data', delimiter '|');"
    //val b: String = "CREATE TABLE S (C int, B string,A date)  USING csv OPTIONS(path 'data/S.data', delimiter '|');"
    //val b: String = "CREATE TABLE T (C int, D int)  USING csv OPTIONS(path 'data/T.data', delimiter '|');"
    while(true){
      println("$>")
      val plan = parseSql(StdIn.readLine())
      plan match {
        case c: CreateTableStatement =>
          //val t1=System.nanoTime()
          var seqattr: Seq[AttributeReference]=Seq()
          for (f <- c.tableSchema) {
            val id = NamedExpression.newExprId
            seqattr = seqattr ++ Seq(AttributeReference(f.name.toUpperCase, f.dataType)(id, c.tableName))
          }
          hm += (c.tableName -> (seqattr, c.location))

          //var table:Iterator[InternalRow]=tableIteration(MyTable(c.tableName))
          //hashData += (c.tableName -> table.toIndexedSeq)
          var dTypes: Seq[DataType]=seqattr.map(f=>f.dataType)
          var open: BufferedSource=Source.fromFile(c.location.get)
          var current: IndexedSeq[String]=open.getLines().toIndexedSeq
          var newSeq:IndexedSeq[InternalRow]=IndexedSeq()
          for(f<-current) {
            val line = f.split('|')
            var count = 0
            var seqNew: Seq[Any] = Seq()
            for (i <- line) {
              seqNew = seqNew ++ Seq(dTypes(count) match {
                case IntegerType => i.toInt
                case FloatType => i.toFloat
                case DoubleType => i.toDouble
                case DateType => parseDate(i)
                case StringType => UTF8String.fromString(i)
              })
              count = count + 1
            }
            val irow=InternalRow.fromSeq(seqNew)
            newSeq=newSeq ++ Seq(irow)
          }
          hashData += (c.tableName -> newSeq)

          /*if(c.options.keys.toSeq.contains("primary_key")) {
            val seqIndex: Seq[String] = c.options("primary_key").split(',')
            var hIndex: Seq[AttributeReference] = Seq()
            for (f <- seqIndex) {
              hIndex = hIndex ++ seqattr.filter(d => f.toUpperCase == d.name)
              //hashIndex += (hIndex -> hashTable(MyTable(c.tableName).it, MyTable(c.tableName), hIndex))
            }
            primaryAtt+= (c.tableName -> hIndex)
          }*/
            if (c.options.keys.toSeq.contains("hash_index")) {
              val seqIndex: Seq[String] = c.options("hash_index").split('|')
              var hIndex: Seq[AttributeReference] = Seq()
              for (f <- seqIndex) {
                hIndex = hIndex ++ seqattr.filter(d => f.toUpperCase == d.name)
                //hashIndex += (hIndex -> hashTable(MyTable(c.tableName).it, MyTable(c.tableName), hIndex))
              }
              hashAtt += (c.tableName -> hIndex)
              var ref=Bref(hIndex.head,seqattr).head
              //hashIndex = hashIndex ++ hashTable(newSeq.iterator, MyTable(c.tableName), hIndex.head)
              //hashIndex= hashIndex ++ newSeq.map{x => (Seq(x.get(ref.ordinal,ref.dataType)),Seq(x))}
              hashIndex= hashIndex ++ newSeq.groupBy(x=> Rowlookup(ref.ordinal,ref).eval(x))
            }
          //println(hashIndex)

          if(c.options.keys.toSeq.contains("tree_index")){
            val seqIndex: Seq[String] = c.options("tree_index").split('|')
            var hIndex: Seq[AttributeReference] = Seq()
            var order:Seq[SortOrder]=Seq()
            for (f <- seqIndex) {
              var newAtt=seqattr.filter(d => f.toUpperCase == d.name)
              hIndex = hIndex ++ newAtt
              var ref=Bref(newAtt.head,seqattr).head
              var sMap:mutable.TreeMap[InternalRow,Seq[InternalRow]]=mutable.TreeMap[InternalRow,Seq[InternalRow]]()(InterpretedOrdering.forSchema(Seq(ref.dataType)))
              sMap= sMap ++ newSeq.groupBy(x => InternalRow.fromSeq(Seq(x.get(ref.ordinal,ref.dataType))))
              treeIndex+= (newAtt.head->sMap)
              //hashIndex += (hIndex -> hashTable(MyTable(c.tableName).it, MyTable(c.tableName), hIndex))
            }
            //println(treeIndex)
            treeAtt+= (c.tableName -> hIndex)
          }

          //println(hashAtt+"\n"+treeAtt)
          //val t1=System.nanoTime()
          /*if(c.tableName.head.toUpperCase.equals("LINEITEM")) {
          hashIndex = hashIndex ++ hashTable(MyTable(c.tableName).it, MyTable(c.tableName), MyTable(c.tableName).tableHashIndex.head)
          }*/
          //val t2=System.nanoTime()
          //println("Total Time"+(t2-t1)/math.pow(10,9))
          //hashIndex.foreach(a=>println(a))
        case _ =>
          //try {
          //val t1=System.nanoTime()
          //println(plan)
            val projanalyzedplan = resolveProjectFilter(plan)
          //println(projanalyzedplan)
            val aggregatePlan = resolveAggregate(projanalyzedplan)
          //println(aggregatePlan)
            val optimizedPlan = fixpoint(aggregatePlan)
            //val optimizedPlan = aggregatePlan
          //println(optimizedPlan)


            /*val it = eval(projanalyzedplan)
            var newBuf=initialize()
            var accumBuf=update(newBuf,it.next())
            while(it.hasNext){
              accumBuf=update(accumBuf,it.next())
            }
            println(accumBuf(0))
            println(evaluate(accumBuf))
            */
            //println(optimizedPlan)



          /*for(f<-optimizedPlan){
            f match{
              //case u:Join=>println(f +""+ u.left +""+ u.right)
              case u:Filter=>println("Filter"+u)
              case u:SubQueryResult=>print("SubQuery"+u.plan)
              case _=>println("")
            }
          }*/


            if (optimizedPlan.resolved) {
              val it = eval(optimizedPlan)
              val outputcols=optimizedPlan.output
              //println(outputcols)
              while(it.hasNext){
                var count=0
                var col=it.next()
                for(f<-outputcols) {
                  print(outputcols(count).dataType match {
                    case DateType => LocalDate.ofEpochDay(col.getInt(count))
                    case _=> col.get(count, outputcols(count).dataType)
                  })
                  if (count != outputcols.length - 1) {
                    print("|")
                  }
                  count=count+1
                }
                println("")
              }
            } else {
              print("")
            }
          //val t2=System.nanoTime()
          //println("Total Time"+(t2-t1)/math.pow(10,9))
          /*}
          catch{
            case _=>System.err
          }*/
      }
    }
  }
}

