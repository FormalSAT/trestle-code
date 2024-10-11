import Lake
open Lake DSL

package Trestle {
  -- add package configuration options here
}

lean_lib Trestle {
  -- add library configuration options here
}

lean_exe SRChecker {
  root := `Trestle.ProofChecking.Checkers.SRCheckerExe
  moreLeancArgs := #["-UNDEBUG", "-g", "-Og", "-ggdb", "-g3", "-fno-omit-frame-pointer"]
}
--@[default_target]
--lean_exe «trestleCode» {
--  root := `Main
--}
