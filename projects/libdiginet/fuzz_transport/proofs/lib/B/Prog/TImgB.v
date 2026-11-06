(* Image B (fuzz_transport.asan-ubsan 41113a03c82f): the addresses the model takes from a timg record
   (TModel/TImg.v), from the symbol table of the image's unstripped twin (e217cb0a84f1, the same allocated sections
   but the build-id note): io_send 0x82ffc, io_recv 0x83368, io_now 0x83410, notice 0x8341c (local FUNC symbols,
   .text); SPEC_C24 0xa3a00, SPEC_PC 0xa3a20, personalities 0xa3b00 (local OBJECT symbols, .data.rel.ro; each
   symbol's size includes its redzone). *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TImg.
From Stdlib Require Import ZArith.
Open Scope Z_scope.

Definition timg_B : timg := TImg 0x82ffc 0x83368 0x83410 0x8341c 0xa3a00 0xa3a20 0xa3b00.
