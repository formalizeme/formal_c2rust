use recordManager::buffer_mgr;
use recordManager::buffer_mgr_stat;
use recordManager::dberror;
use recordManager::dt;
use recordManager::expr;
use recordManager::record_mgr;
use recordManager::rm_serializer;
use recordManager::storage_mgr;
use recordManager::tables;

#[test]
pub fn test_value_serialize(){
    // assert that the value equals a string

    assert_eq!(rm_serializer::serialize_value(&rm_serializer::string_to_value("i10")), "10");
    assert_eq!(rm_serializer::serialize_value(&rm_serializer::string_to_value("f5.3")), "5.300000");
    assert_eq!(rm_serializer::serialize_value(&rm_serializer::string_to_value("sHello World")), "Hello World");
    assert_eq!(rm_serializer::serialize_value(&rm_serializer::string_to_value("bt")), "true");
    assert_eq!(rm_serializer::serialize_value(&rm_serializer::string_to_value("btrue")), "true");
}

/// Equivalent to C's OP_TRUE macro:
///   op(left, right, result); assert(result->v.boolV == true);
fn op_true(
    left: &str, right: &str,
    op: fn(&tables::Value, &tables::Value, &mut tables::Value) -> dberror::RC,
    msg: &str,
) {
    let mut result = tables::make_value(&tables::DataType::DtInt.to_string(), "0");
    let rc = op(&rm_serializer::string_to_value(left), &rm_serializer::string_to_value(right), &mut result);
    assert_eq!(rc, dberror::RC::Ok, "{}", msg);
    match result.v {
        tables::ValueUnion::BoolV(b) => assert!(b, "{}", msg),
        _ => panic!("{}: result is not a boolean", msg),
    }
}

/// Equivalent to C's OP_FALSE macro:
///   op(left, right, result); assert(result->v.boolV == false);
fn op_false(
    left: &str, right: &str,
    op: fn(&tables::Value, &tables::Value, &mut tables::Value) -> dberror::RC,
    msg: &str,
) {
    let mut result = tables::make_value(&tables::DataType::DtInt.to_string(), "0");
    let rc = op(&rm_serializer::string_to_value(left), &rm_serializer::string_to_value(right), &mut result);
    assert_eq!(rc, dberror::RC::Ok, "{}", msg);
    match result.v {
        tables::ValueUnion::BoolV(b) => assert!(!b, "{}", msg),
        _ => panic!("{}: result is not a boolean", msg),
    }
}

#[test]
pub fn testOperators(){
    let mut result = tables::make_value(&tables::DataType::DtInt.to_string(), "0");

    // equality
    op_true("i10", "i10", expr::value_equals, "10 = 10");
    op_false("i9", "i10", expr::value_equals, "9 != 10");
    op_true("sHello World", "sHello World", expr::value_equals, "Hello World = Hello World");
    op_false("sHello Worl", "sHello World", expr::value_equals, "Hello Worl != Hello World");
    op_false("sHello Worl", "sHello Wor", expr::value_equals, "Hello Worl != Hello Wor");

    // smaller
    op_true("i3", "i10", expr::value_smaller, "3 < 10");
    op_true("f5.0", "f6.5", expr::value_smaller, "5.0 < 6.5");

    // boolean
    op_true("bt", "bt", expr::bool_and, "t AND t = t");
    op_false("bt", "bf", expr::bool_and, "t AND f = f");

    op_true("bt", "bf", expr::bool_or, "t OR f = t");
    op_false("bf", "bf", expr::bool_or, "f OR f = f");

    // boolNot
    assert_eq!(expr::bool_not(&rm_serializer::string_to_value("bf"), &mut result), dberror::RC::Ok);
    match result.v {
        tables::ValueUnion::BoolV(b) => assert!(b, "!f = t"),
        _ => panic!("!f = t: result is not a boolean"),
    }
}

#[test]
fn test_expressions() {
    let mut res = tables::Value {
        dt: tables::DataType::DtInt, // Placeholder, will be overwritten
        v: tables::ValueUnion::IntV(0),
    };

    println!("Running test: test complex expressions");

    // Creating a constant value expression (10)
    let l = expr::Expr {
        expr_type: expr::ExprType::ExprConst,
        expr: expr::ExprUnion::Cons(rm_serializer::string_to_value("i10")),
    };
    expr::eval_expr(&tables::Record { id: tables::RID { page: 0, slot: 0 }, data: String::new() }, &tables::Schema {
        num_attr: 0,
        attr_names: vec![],
        data_types: vec![],
        type_length: vec![],
        key_attrs: vec![],
        key_size: 0,
    }, &l, &mut res);
    let mut res2 = tables::Value {
        dt: tables::DataType::DtInt, // Placeholder, will be overwritten
        v: tables::ValueUnion::IntV(0),
    }; 
    assert!(expr::value_equals(&rm_serializer::string_to_value("i10"), &res, &mut res2) == dberror::RC::Ok, "Const 10");

    // Creating a constant value expression (20)
    let r = expr::Expr {
        expr_type: expr::ExprType::ExprConst,
        expr: expr::ExprUnion::Cons(rm_serializer::string_to_value("i20")),
    };
    expr::eval_expr(&tables::Record { id: tables::RID { page: 0, slot: 0 }, data: String::new() }, &tables::Schema {
        num_attr: 0,
        attr_names: vec![],
        data_types: vec![],
        type_length: vec![],
        key_attrs: vec![],
        key_size: 0,
    }, &r, &mut res);
    let mut res2 = tables::Value {
        dt: tables::DataType::DtInt, // Placeholder, will be overwritten
        v: tables::ValueUnion::IntV(0),
    }; 
    assert!(expr::value_equals(&rm_serializer::string_to_value("i20"), &res, &mut res2) == dberror::RC::Ok, "Const 20");

    // Creating a binary operation expression (10 < 20)
    let op = expr::Expr {
        expr_type: expr::ExprType::ExprOp,
        expr: expr::ExprUnion::Op(Box::new(expr::Operator {
            op_type: expr::OpType::OpCompSmaller,
            args: vec![l.clone(), r.clone()],
        })),
    };
    expr::eval_expr(&tables::Record { id: tables::RID { page: 0, slot: 0 }, data: String::new() }, &tables::Schema {
        num_attr: 0,
        attr_names: vec![],
        data_types: vec![],
        type_length: vec![],
        key_attrs: vec![],
        key_size: 0,
    }, &op, &mut res);
    let mut res2 = tables::Value {
        dt: tables::DataType::DtInt, // Placeholder, will be overwritten
        v: tables::ValueUnion::IntV(0),
    }; 
    assert!(expr::value_equals(&rm_serializer::string_to_value("bt"), &res, &mut res2) == dberror::RC::Ok, "Const 10 < Const 20");

    // Creating a constant boolean value expression (true)
    let l = expr::Expr {
        expr_type: expr::ExprType::ExprConst,
        expr: expr::ExprUnion::Cons(rm_serializer::string_to_value("bt")),
    };
    expr::eval_expr(&tables::Record { id: tables::RID { page: 0, slot: 0 }, data: String::new() }, &tables::Schema {
        num_attr: 0,
        attr_names: vec![],
        data_types: vec![],
        type_length: vec![],
        key_attrs: vec![],
        key_size: 0,
    }, &l, &mut res);
    let mut res2 = tables::Value {
        dt: tables::DataType::DtInt, // Placeholder, will be overwritten
        v: tables::ValueUnion::IntV(0),
    }; 
    assert!(expr::value_equals(&rm_serializer::string_to_value("bt"), &res, &mut res2) == dberror::RC::Ok, "Const true");

    // Logical AND: (10 < 20) AND true
    let op = expr::Expr {
        expr_type: expr::ExprType::ExprOp,
        expr: expr::ExprUnion::Op(Box::new(expr::Operator {
            op_type: expr::OpType::OpBoolAnd,
            args: vec![op.clone(), l.clone()],
        })),
    };
    expr::eval_expr(&tables::Record { id: tables::RID { page: 0, slot: 0 }, data: String::new() }, &tables::Schema {
        num_attr: 0,
        attr_names: vec![],
        data_types: vec![],
        type_length: vec![],
        key_attrs: vec![],
        key_size: 0,
    }, &op, &mut res);
    let mut res2 = tables::Value {
        dt: tables::DataType::DtInt, // Placeholder, will be overwritten
        v: tables::ValueUnion::IntV(0),
    }; 
    assert!(expr::value_equals(&rm_serializer::string_to_value("bt"), &res, &mut res2) == dberror::RC::Ok, "(Const 10 < Const 20) AND true");

    println!("Test Done.");
}
fn main(){}