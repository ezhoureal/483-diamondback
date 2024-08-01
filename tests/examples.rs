use snake::runner;

macro_rules! mk_test {
    ($test_name:ident, $file_name:expr, $expected_output:expr) => {
        #[test]
        fn $test_name() -> std::io::Result<()> {
            test_example_file($file_name, $expected_output)
        }
    };
}

macro_rules! mk_fail_test {
    ($test_name:ident, $file_name:expr, $expected_output:expr) => {
        #[test]
        fn $test_name() -> std::io::Result<()> {
            test_example_fail($file_name, $expected_output)
        }
    };
}

/*
 * YOUR TESTS GO HERE
 */
mk_fail_test!(
    parse_error_example,
    "parse_error.adder",
    "Unrecognized token `)`"
);
mk_fail_test!(err_1, "err_1", "Error generating assembly");
mk_fail_test!(err_2, "err_2", "overflow");
mk_fail_test!(err_3, "err_3", "arithmetic expected a number");
mk_fail_test!(err_4, "err_4", "arithmetic expected a number");
mk_fail_test!(err_5, "err_5", "overflow");
mk_fail_test!(err_6, "err_6", "overflow");
mk_fail_test!(err_7, "err_7", "arithmetic expected a number");
mk_fail_test!(err_8, "err_8", "overflow");
mk_fail_test!(err_9, "err_9", "arithmetic expected a number");
mk_fail_test!(err_10, "err_10", "if expected a boolean");
mk_fail_test!(logic_error_1, "logic_error_1", "logic expected a boolean");
mk_fail_test!(logic_error_2, "logic_error_2", "logic expected a boolean");
mk_fail_test!(logic_error_3, "logic_error_3", "logic expected a boolean");
mk_fail_test!(cmp_err_1, "cmp_err_1", "comparison expected a number");
mk_fail_test!(cmp_err_2, "cmp_err_2", "comparison expected a number");
mk_fail_test!(cmp_err_3, "cmp_err_3", "comparison expected a number");
mk_fail_test!(cmp_err_4, "cmp_err_4", "comparison expected a number");
mk_test!(test_1, "test_1", "4");
mk_test!(test_2, "test_2", "6");
mk_test!(test_3, "test_3", "4");
mk_test!(test_4, "test_4", "5");
mk_test!(test_5, "test_5", "3");
mk_test!(test_6, "test_6", "3");
mk_test!(test_7, "test_7", "3");
mk_test!(test_8, "test_8", "33");
mk_test!(test_9, "test_9", "6");
mk_test!(test_10, "test_10", "true");
mk_test!(test_11, "test_11", "true");
mk_test!(test_12, "test_12", "false");
mk_test!(test_13, "test_13", "true");
mk_test!(test_14, "test_14", "false");
mk_test!(test_15, "test_15", "false");
mk_test!(test_16, "test_16", "true");
mk_test!(test_17, "test_17", "false");
mk_test!(test_18, "test_18", "true");
mk_test!(test_19, "test_19", "false");
mk_test!(test_20, "test_20", "false");
mk_test!(test_21, "test_21", "true");
mk_test!(test_22, "test_22", "true");
mk_test!(test_23, "test_23", "false");
mk_test!(test_24, "test_24", "true");
mk_test!(test_25, "test_25", "false");
mk_test!(test_26, "test_26", "true");
mk_test!(test_27, "test_27", "false");
mk_test!(test_28, "test_28", "-4611686018427387902");
mk_test!(test_29, "test_29", "4000000000000000000");
mk_test!(test_30, "test_30", "true");
mk_test!(test_31, "test_31", "3922\n3922");
mk_test!(test_32, "test_32", "2\n4\n4");

// IMPLEMENTATION
fn test_example_file(f: &str, expected_str: &str) -> std::io::Result<()> {
    use std::path::Path;
    let p_name = format!("examples/{}", f);
    let path = Path::new(&p_name);

    // Test the compiler
    let tmp_dir = tempfile::TempDir::new()?;
    let mut w = Vec::new();
    match runner::compile_and_run_file(&path, tmp_dir.path(), &mut w) {
        Ok(()) => {
            let stdout = std::str::from_utf8(&w).unwrap();
            assert_eq!(stdout.trim(), expected_str)
        }
        Err(e) => {
            assert!(false, "Expected {}, got an error: {}", expected_str, e)
        }
    }

    Ok(())
}

fn test_example_fail(f: &str, includes: &str) -> std::io::Result<()> {
    use std::path::Path;
    let p_name = format!("examples/{}", f);
    let path = Path::new(&p_name);

    // Test the compiler
    let tmp_dir = tempfile::TempDir::new()?;
    let mut w_run = Vec::new();
    match runner::compile_and_run_file(
        &Path::new(&format!("examples/{}", f)),
        tmp_dir.path(),
        &mut w_run,
    ) {
        Ok(()) => {
            let stdout = std::str::from_utf8(&w_run).unwrap();
            assert!(false, "Expected a failure but got: {}", stdout.trim())
        }
        Err(e) => {
            let msg = format!("{}", e);
            assert!(
                msg.contains(includes),
                "Expected error message to include the string \"{}\" but got the error: {}",
                includes,
                msg
            )
        }
    }

    Ok(())
}
