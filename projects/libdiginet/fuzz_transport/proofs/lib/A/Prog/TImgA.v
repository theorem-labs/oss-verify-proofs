(* Image A (fuzz_transport.asan e89be137db17): the addresses the model takes from a timg record (TModel/TImg.v), from
   the symbol table of the image's unstripped twin (86efc3a80314, the same allocated sections but the build-id note):
   io_send 0x82d60, io_recv 0x834c4, io_now 0x8356c, notice 0x83578 (local FUNC symbols, .text); SPEC_C24 0xa3da0,
   SPEC_PC 0xa3dc0, personalities 0xa3ea0 (local OBJECT symbols, .data.rel.ro; each symbol's size includes its
   redzone). *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TImg.
From Stdlib Require Import ZArith.
Open Scope Z_scope.

Definition timg_A : timg := TImg 0x82d60 0x834c4 0x8356c 0x83578 0xa3da0 0xa3dc0 0xa3ea0.
