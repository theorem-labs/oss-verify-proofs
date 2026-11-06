(* The plain image's addresses for the fuzz_transport harness model. *)
(* Values from the plain image's symbol table (nm of the plain fuzz_transport binary):
   io_send 0x144ec, io_recv 0x1492c, io_now 0x149d8, notice 0x149e4 (all `t`); SPEC_C24 0x213e8, SPEC_PC 0x213f8,
   personalities 0x21420 (.data.rel.ro; the LPS memory image maps that segment read-write, PT_GNU_RELRO is not applied, so a contract that reads these records asks for them unchanged: TContract's relro_img). The world base is W_BASE_PLAIN. *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TImg.
From Stdlib Require Import ZArith.
Open Scope Z_scope.

Definition timg_plain : timg := TImg 0x144ec 0x1492c 0x149d8 0x149e4 0x213e8 0x213f8 0x21420.
