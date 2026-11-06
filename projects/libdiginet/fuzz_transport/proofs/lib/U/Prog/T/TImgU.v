(* The ubsan image's addresses for the fuzz_transport harness model. *)
(* Values from the ubsan image's symbol table (nm of the ubsan fuzz_transport binary):
   io_send 0x1482c, io_recv 0x14b20, io_now 0x14bbc, notice 0x14bc8 (all `t`); SPEC_C24 0x21f18, SPEC_PC 0x21f28,
   personalities 0x21f90 (.data.rel.ro; the LPS memory image maps that segment read-write, PT_GNU_RELRO is not applied, so a contract that reads these records asks for them unchanged: TContract's relro_img). The world base is W_BASE_UBSAN. *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TImg.
From Stdlib Require Import ZArith.
Open Scope Z_scope.

Definition timg_ubsan : timg := TImg 0x1482c 0x14b20 0x14bbc 0x14bc8 0x21f18 0x21f28 0x21f90.
