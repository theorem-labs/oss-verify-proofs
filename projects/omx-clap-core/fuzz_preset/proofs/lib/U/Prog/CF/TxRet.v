From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require Import Contract.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import TxCalls.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF Require Import tx_put_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF Require Import SRCF.
Import ListNotations.
Local Open Scope Z_scope.

Section K.
Context {fx : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.FPState} {rc : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Variable F : ResForm.
Let segs := ms_segs B.
Let MR := aa_MR API.

Definition tx_start (stk : Z) (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte)
    (md : Model) (t b0 len0 cap0 : Z) (txt : list byte) (bnd : rf_R F) (ns : list Z) (need : Z) : Prop :=
  call_pre_k B MR stk L A regs mem md /\ st_init_done A = true /\ ro_agree segs mem /\
  getr regs 10 = Z_to_bv 64 t /\
  spZ regs <= t /\ t + 24 <= 2 ^ 64 /\ t mod 8 = 0 /\
  (forall i, 0 <= i < 24 -> writable_at segs mem (t + i)) /\
  0 <= b0 < 2 ^ 64 /\ 0 <= len0 < 2 ^ 64 /\ 0 <= cap0 < 2 ^ 64 /\
  text_rec B mem t b0 len0 cap0 /\ tx_inv B L A mem b0 len0 cap0 txt /\
  need <= 2 ^ 28 /\ rf_ok F A bnd /\ tx_rooms F bnd len0 cap0 ns.

Definition tx_relx (stk : Z) (regs : bvmap 5 word) (t b0 len0 cap0 : Z) (txt add : list byte) (bnd : rf_R F)
    (L : layout) (A : astate) (mem : word -> option byte) (md : Model)
    (L' : layout) (A' : astate) (mem' : word -> option byte) (md' : Model) (b1 cap1 : Z) (ks : list Z) : Prop :=
  tx_frame B API stk regs (tx_writes t b0 cap0 b1 cap1) L A mem md L' A' mem' md' /\
  (length (st_regions A) <= length (st_regions A'))%nat /\
  blocks_kept B L A mem mem' (fun a => a = b0) /\
  (forall a k, In (a, k) (blocks L A) -> (a, k) <> (b0, cap0) -> In (a, k) (blocks L' A') /\ (a, k) <> (b1, cap1)) /\
  (forall a k, In (a, k) (blocks L A) -> 0 < k -> a <> b0 -> a <> b1) /\
  text_rec B mem' t b1 (len0 + Z.of_nat (length add)) cap1 /\
  (forall i, 0 <= i < 24 -> writable_at segs mem' (t + i)) /\
  tx_inv B L' A' mem' b1 (len0 + Z.of_nat (length add)) cap1 (txt ++ add) /\
  ro_agree segs mem' /\ guard_kept B mem mem' /\ st_init_done A' = true /\
  zsum ks = Z.of_nat (length add) /\ cap1 = tx_capf len0 cap0 ks /\ rf_ok F A' (tx_fold F bnd len0 cap0 ks).

Definition tx_rel (stk : Z) (regs : bvmap 5 word) (t b0 len0 cap0 : Z) (txt add : list byte) (ks : list Z)
    (bnd : rf_R F) (L : layout) (A : astate) (mem : word -> option byte) (md : Model)
    (L' : layout) (A' : astate) (mem' : word -> option byte) (md' : Model) : Prop :=
  exists b1 cap1, tx_relx stk regs t b0 len0 cap0 txt add bnd L A mem md L' A' mem' md' b1 cap1 ks.

Definition tx_ret (stk : Z) (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte)
    (md : Model) (t b0 len0 cap0 : Z) (txt add : list byte) (ks : list Z) (bnd : rf_R F)
    (Q : layout -> astate -> (word -> option byte) -> Prop) (c' : config) : Prop :=
  exists L' A' regs' mem' md',
    c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom segs)) md' /\
    regs_preserved regs regs' /\
    tx_rel stk regs t b0 len0 cap0 txt add ks bnd L A mem md L' A' mem' md' /\
    Q L' A' mem'.

End K.
