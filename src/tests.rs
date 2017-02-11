use super::*;

fn foo() -> Result<(), Failure> {
    failed!("foo");
    Ok(())
}

fn bar(input: usize) -> Result<(), Failure> {
    may_fail!(foo(), "input={}", input)?;
    Ok(())
}

#[test]
fn it_works() {
    assert_eq!(format!("\n{}", foo().err().unwrap()),
               r#"
Failed; foo
  TRACE:
    [0] failure::tests#src\tests.rs:4
"#);

    assert_eq!(format!("\n{}", bar(4).err().unwrap()),
               r#"
Failed; foo
  TRACE:
    [0] failure::tests#src\tests.rs:4
    [1] failure::tests#src\tests.rs:9; input=4
"#);
}
