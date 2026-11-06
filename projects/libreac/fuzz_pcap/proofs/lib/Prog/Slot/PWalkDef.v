From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog Require Import StdioModel pcap_source_struct_next.
Import ListNotations.
Open Scope Z_scope.

(* skips sw F cap q Q: from file position q, the records of kind KEmpty and KBig come one after the other
   and the first record of another kind starts at Q. Both loops of the slot that walk the file (the record
   loop at 0x12dfc and the end loop at 0x13080) pass these records; the reader's chain passes the same ones. *)
Inductive skips (sw : bool) (F : list byte) (cap : Z) : Z -> Z -> Prop :=
| skips_stop : forall q,
    kind sw F cap q <> KEmpty -> kind sw F cap q <> KBig -> skips sw F cap q q
| skips_empty : forall q Q,
    kind sw F cap q = KEmpty -> skips sw F cap (q + 16) Q -> skips sw F cap q Q
| skips_big : forall q Q,
    kind sw F cap q = KBig -> skips sw F cap (q + 16 + incl sw F q) Q -> skips sw F cap q Q.

(* The answer the end loop of the slot (0x13080-0x13100) computes when it stops at Q. *)
Definition want_of (sw : bool) (F : list byte) (cap Q : Z) : Z :=
  match kind sw F cap Q with
  | KEnd => 0
  | KFit => incl sw F Q
  | _ => -1
  end.
