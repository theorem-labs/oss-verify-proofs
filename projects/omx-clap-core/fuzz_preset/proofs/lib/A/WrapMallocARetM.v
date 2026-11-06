(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: omx-clap-core/fuzz_preset image A (asan, pin 1be0f53d96cb, unstripped twin bff8519bbe3e;
   relocated from d83eb25d by symbol + offset, the internal file RELOC102-A1.md), the
   MACHINE RUNS of the malloc interceptor's RETURN segment: Allocate's return into asan_malloc (RA_ALLOC, A 0x32588)
   -> the wrapper's return to its caller, register / memory facts in, register / memory facts out (no allocator
   invariant here; WrapMallocARet.v is the glue to the record field wm_ret).
   Method: plugin-hostd/fuzz_reply's lib/A/RGthinM2.v m6a / m6b at a working branch 66a127cb11e (the same
   SRr framework, asan_realloc's NULL-input call there), ported onto asan_malloc's and ___interceptor_malloc's
   epilogues; SetErrnoToENOMEM and __errno_location are the same code. Rule 24: the internal file RULE24-W6PRE.md.
   THE CODE (capstone over the pinned image 1be0f53d; RV64, no compressed instructions), read through
   AB1q.tfibtbl_rtA (its rows 0x3255c / 633, 0x53734 / 206, 0x6d398 / 8, 0x8efd8 / 3 cover every instruction):
     asan_malloc  0x32588 beqz a0, +0x14        (Allocate's return; taken on NULL -> 0x3259c)
                  0x3258c ld ra, 8(sp)          (= RA_ASAN_MALLOC, ___interceptor_malloc + 0x134)
                  0x32590 ld s0, 0(sp); 0x32594 addi sp, sp, 0x10; 0x32598 ret
                  0x3259c mv s0, a0; 0x325a0 jal SetErrnoToENOMEM (0x6d398, ra = 0x325a4); 0x325a4 mv a0, s0;
                  0x325a8 ld ra, 8(sp); 0x325ac ld s0, 0(sp); 0x325b0 addi sp, sp, 0x10; 0x325b4 ret
     SetErrnoToENOMEM 0x6d398: addi sp, sp, -0x10; sd ra, 8(sp); jal __errno_location (0x8efd8); addi a1, zero, 0xc;
                  sw a1, 0(a0); ld ra, 8(sp); addi sp, sp, 0x10; ret
     __errno_location 0x8efd8: mv a0, tp; addi a0, a0, -0xa4; ret            (errno = tp - 0xa4 = TFIB_ERRNO)
     ___interceptor_malloc 0x53a44 addi sp, sp, 0x60; 0x53a48..0x53a60 ld ra, s0, s1, s2, s3, s4, s5 from
                  0x7e8 .. 0x7b8(sp); 0x53a64 addi sp, sp, 0x7f0; 0x53a68 ret
   The frames, relative to the sp at the start (spA = the caller's sp - 2144): asan_malloc's 16 bytes at spA (ra at
   spA + 8), the interceptor's saved ra, s0..s5 at spA + 2136 .. spA + 2088 (the caller's sp - 8 .. - 56).
   No Admitted / Axiom. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v AB1q AB13 AF0l AF0m AF0x.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1w WrapMallocAConsts.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Definition c8m (o : Z) (e : sv) : YP09.chunk := YP09.mkChunk o (CVal 8 e).

(* The frame regions, based at atom 2 (the sp at the start). Atoms 32..38: the interceptor's saved ra, s0..s5; atom
   39: asan_malloc's saved s0 (asan_malloc's epilogue loads it before the interceptor's reloads s0). *)
Definition AFRm : YP09.region := YP09.mkRegion (Some 2%nat) 0 16 0 0 [c8m 0 (SOff 39 0); c8m 8 (SLit RA_ASAN_MALLOC)].
Definition IFRm (b : Z) : YP09.region := YP09.mkRegion (Some 2%nat) b (b + 56) 0 0
[c8m b (SOff 38 0); c8m (b + 8) (SOff 37 0); c8m (b + 16) (SOff 36 0); c8m (b + 24) (SOff 35 0);
 c8m (b + 32) (SOff 34 0); c8m (b + 40) (SOff 33 0); c8m (b + 48) (SOff 32 0)].
(* errno, based at atom 4 (tp): __errno_location's tp - 0xa4. *)
Definition ERRm : YP09.region := YP09.mkRegion (Some 4%nat) (-164) (-160) (-164) (-160) [].
(* SetErrnoToENOMEM's frame below the start sp. *)
Definition ESFm : YP09.region := YP09.mkRegion (Some 2%nat) (-16) 0 (-16) 0 [].
Definition IFR_OFF : Z := 2088.
Definition SNm : sstate := mkSS RA_ALLOC sr_atoms [ESFm; AFRm; IFRm IFR_OFF; ERRm] None (mkFacts [] [] []).
Definition SBm : sstate := mkSS RA_ALLOC sr_atoms [AFRm; IFRm IFR_OFF] None (mkFacts [] [] []).

Definition xvm (vra vs0 vs1 vs2 vs3 vs4 vs5 w0 : Z) : list word :=
[w64 vra; w64 vs0; w64 vs1; w64 vs2; w64 vs3; w64 vs4; w64 vs5; w64 w0].

Lemma val_mem_addr_m : forall m a a' (n : nat) v, val_mem tfibsegs m a n v -> a = a' -> val_mem tfibsegs m a' n v.
Proof. intros m a a' n v H <-. exact H. Qed.
Lemma apresent_wr_m : forall (H : word -> bool) (mem : word -> option byte) a,
apresent H mem a -> writable_at tfibsegs (mrestrict H mem) a.
Proof. intros H m a [Hh [b Hb]]. unfold writable_at, wview, mrestrict. rewrite Hh, Hb. discriminate. Qed.
(* AB13.tfib_rw_window's window: the image's writable pages. *)
Lemma rw_wr_m : forall (m : word -> option byte) a, 0xa1000 <= a < 0x600000 -> writable_at tfibsegs m a.
Proof. intros m a Ha. unfold writable_at. apply AB13.tfib_rw_window. rewrite unsigned_lit_small by lia. exact Ha. Qed.
Lemma TFIB_ERRNO_tp : TFIB_ERRNO = TFIB_TP - 164.
Proof. reflexivity. Qed.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma chunk8_atom_m : forall regs (extra : list word) m base off j v,
nth j extra (Z_to_bv 64 0) = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> val_mem tfibsegs m (base + off) 8 v ->
YP09.chunk_ok tfibsegs (Ereg regs extra) m base (c8m off (SOff (32 + j) 0)).
Proof.
intros regs extra m base off j v Hn Hv Hm. apply (chunk_ok_val tfibsegs _ m base off 8 (SOff (32 + j) 0) v); [|cbn; lia|cbn; lia|exact Hm].
cbn [sv_denot]. rewrite ew_Ereg_extra, Hn. rewrite unsigned_lit_small by lia. f_equal; lia.
Qed.
Lemma chunk8_lit_m : forall E m base off v, 0 <= v < 2 ^ 64 -> val_mem tfibsegs m (base + off) 8 v ->
YP09.chunk_ok tfibsegs E m base (c8m off (SLit v)).
Proof. intros E m base off v Hv Hm. apply (chunk_ok_val tfibsegs E m base off 8 (SLit v) v); [reflexivity|cbn; lia|cbn; lia|exact Hm]. Qed.
Lemma vm_vis_m : forall (H : word -> bool) mem a (w : nat) v i, val_mem tfibsegs (mrestrict H mem) a w v -> 0 <= i < Z.of_nat w ->
aview tfibsegs H mem (a + i) <> None.
Proof.
intros H mem a w v i Hv Hi. unfold aview. replace i with (Z.of_nat (Z.to_nat i)) by lia. rewrite (Hv (Z.to_nat i) ltac:(lia)). discriminate.
Qed.

Section W.
Variable W : world tfibsegs.
Variable md : Model.
Local Notation H := (w_H W).

Definition afr_okm (m : word -> option byte) (a w0 : Z) : Prop :=
val_mem tfibsegs (mrestrict H m) a 8 w0 /\ val_mem tfibsegs (mrestrict H m) (a + 8) 8 RA_ASAN_MALLOC.
Definition ifr_okm (m : word -> option byte) (a vra vs0 vs1 vs2 vs3 vs4 vs5 : Z) : Prop :=
val_mem tfibsegs (mrestrict H m) (a + 48) 8 vra /\ val_mem tfibsegs (mrestrict H m) (a + 40) 8 vs0 /\
val_mem tfibsegs (mrestrict H m) (a + 32) 8 vs1 /\ val_mem tfibsegs (mrestrict H m) (a + 24) 8 vs2 /\
val_mem tfibsegs (mrestrict H m) (a + 16) 8 vs3 /\ val_mem tfibsegs (mrestrict H m) (a + 8) 8 vs4 /\
val_mem tfibsegs (mrestrict H m) a 8 vs5.

(* The wrapper's return: the interceptor's callee-saved registers restored from its frame, a0 = [a0], memory [MR]. *)
Definition ret_postm (regs : bvmap 5 word) (MR : (word -> option byte) -> Prop) (sp' a0 vra vs0 vs1 vs2 vs3 vs4 vs5 : Z)
(W' : world tfibsegs) (c' : config) : Prop :=
W' = W /\ exists regs' mem' mat,
c' = mkCfg (mkst regs' (w64 vra) mem' (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md) mat md) /\ MR mem' /\
getr regs' 2 = w64 sp' /\ getr regs' 1 = w64 vra /\ getr regs' 8 = w64 vs0 /\ getr regs' 9 = w64 vs1 /\
getr regs' 18 = w64 vs2 /\ getr regs' 19 = w64 vs3 /\ getr regs' 20 = w64 vs4 /\ getr regs' 21 = w64 vs5 /\
getr regs' 10 = w64 a0 /\
(forall r : bv 5, In r [3; 4; 22; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr regs r).

Ltac reg_ent HS r k :=
let R := fresh "R" in rreg HS r R; rewrite R; exact (ew_Ereg_nat _ _ k r eq_refl).
Ltac reg_x HS r j :=
let R := fresh "R" in rreg HS r R; rewrite R; exact (ew_Ereg_extra _ _ j).
Ltac range7 := match goal with RV : Forall _ _ |- _ =>
  repeat (apply Forall_cons_iff in RV as [? RV]) end.

Ltac ifr_chunks regs X m sp b vra vs0 vs1 vs2 vs3 vs4 vs5 I0 I1 I2 I3 I4 I5 I6 :=
  apply Forall_cons; [apply (chunk8_atom_m regs X m sp b 6 vs5); [reflexivity|lia|eapply val_mem_addr_m; [exact I6|lia]]|];
  apply Forall_cons; [apply (chunk8_atom_m regs X m sp (b + 8) 5 vs4); [reflexivity|lia|eapply val_mem_addr_m; [exact I5|lia]]|];
  apply Forall_cons; [apply (chunk8_atom_m regs X m sp (b + 16) 4 vs3); [reflexivity|lia|eapply val_mem_addr_m; [exact I4|lia]]|];
  apply Forall_cons; [apply (chunk8_atom_m regs X m sp (b + 24) 3 vs2); [reflexivity|lia|eapply val_mem_addr_m; [exact I3|lia]]|];
  apply Forall_cons; [apply (chunk8_atom_m regs X m sp (b + 32) 2 vs1); [reflexivity|lia|eapply val_mem_addr_m; [exact I2|lia]]|];
  apply Forall_cons; [apply (chunk8_atom_m regs X m sp (b + 40) 1 vs0); [reflexivity|lia|eapply val_mem_addr_m; [exact I1|lia]]|];
  apply Forall_cons; [apply (chunk8_atom_m regs X m sp (b + 48) 0 vra); [reflexivity|lia|eapply val_mem_addr_m; [exact I0|lia]]|];
  apply Forall_nil.

(* The memory at the wrapper's return on the ENOMEM path: changed only in a stack window [lo, hi) and errno; errno
   holds 12; the window stays present; every visible byte stays visible. *)
Definition MRerrm (mem : word -> option byte) (lo hi : Z) (m' : word -> option byte) : Prop :=
(forall x : word, ~ (lo <= bv_unsigned x < hi) -> ~ (TFIB_ERRNO <= bv_unsigned x < TFIB_ERRNO + 4) -> m' x = mem x) /\
val_mem tfibsegs (mrestrict H m') TFIB_ERRNO 4 12 /\ (forall a, lo <= a < hi -> apresent H m' a) /\
(forall a, 0 <= a < 2 ^ 64 -> aview tfibsegs H mem a <> None -> aview tfibsegs H m' a <> None).

Lemma vis_keep_m : forall (mem m' : word -> option byte) lo hi a, 0 <= a < 2 ^ 64 ->
(forall x : word, ~ (lo <= bv_unsigned x < hi) -> ~ (TFIB_ERRNO <= bv_unsigned x < TFIB_ERRNO + 4) -> m' x = mem x) ->
val_mem tfibsegs (mrestrict H m') TFIB_ERRNO 4 12 -> (forall a, lo <= a < hi -> apresent H m' a) ->
aview tfibsegs H mem a <> None -> aview tfibsegs H m' a <> None.
Proof.
intros mem m' lo hi a Ha MEQ V P Hv.
destruct (Z_lt_le_dec a lo) as [L1|L1]; [|destruct (Z_lt_le_dec a hi) as [L2|L2]].
3: destruct (Z_lt_le_dec a TFIB_ERRNO) as [L3|L3]; [|destruct (Z_lt_le_dec a (TFIB_ERRNO + 4)) as [L4|L4]].
- destruct (Z_lt_le_dec a TFIB_ERRNO) as [L3|L3]; [|destruct (Z_lt_le_dec a (TFIB_ERRNO + 4)) as [L4|L4]].
  + rewrite (aview_same H mem m' a). exact Hv. apply MEQ; rewrite unsigned_lit_small by lia; lia.
  + replace a with (TFIB_ERRNO + (a - TFIB_ERRNO)) by lia. apply (vm_vis_m H m' TFIB_ERRNO 4 12); [exact V | cbn; lia].
  + rewrite (aview_same H mem m' a). exact Hv. apply MEQ; rewrite unsigned_lit_small by lia; lia.
- destruct (P a ltac:(lia)) as [Hh [b Hb]]. unfold aview, mbyte, mrestrict. rewrite Hh, Hb. discriminate.
- rewrite (aview_same H mem m' a). exact Hv. apply MEQ; rewrite unsigned_lit_small by lia; lia.
- replace a with (TFIB_ERRNO + (a - TFIB_ERRNO)) by lia. apply (vm_vis_m H m' TFIB_ERRNO 4 12); [exact V | cbn; lia].
- rewrite (aview_same H mem m' a). exact Hv. apply MEQ; rewrite unsigned_lit_small by lia; lia.
Qed.

Ltac ret_regs HS E2 Hret msA vra :=
  eapply (SRr_ret_at tfibsegs tfibtbl_rtA tfibtbl_rtA_ok ltac:(assumption) W _); [exact HS | reflexivity | vm_compute; reflexivity |];
  let mat' := fresh "mat" in intros mat'; split; [reflexivity|];
  let R1 := fresh "R1" in assert (R1 : getr (ms_regs msA) 1 = w64 vra) by reg_x HS (1%bv : bv 5) 0%nat;
  exists (ms_regs msA), (ms_mem msA), mat';
  split; [rewrite R1; unfold YK0s.ret_ok in Hret; rewrite Hret; reflexivity|].
Ltac ret_tail HS E2 :=
  split; [let R := fresh "R" in rreg HS (2%bv : bv 5) R; rewrite R, E2; reflexivity|];
  split; [assumption|];
  split; [reg_x HS (8%bv : bv 5) 1%nat|]; split; [reg_x HS (9%bv : bv 5) 2%nat|]; split; [reg_x HS (18%bv : bv 5) 3%nat|];
  split; [reg_x HS (19%bv : bv 5) 4%nat|]; split; [reg_x HS (20%bv : bv 5) 5%nat|]; split; [reg_x HS (21%bv : bv 5) 6%nat|].
Ltac ret_keep HS :=
  let r := fresh "r" in let Hr := fresh "Hr" in intros r Hr; cbn [In] in Hr;
  repeat (destruct Hr as [<-|Hr]; [ lazymatch goal with |- getr _ ?rr = _ =>
    let k := eval vm_compute in (Z.to_nat (bv_unsigned rr)) in reg_ent HS rr k end |]);
  destruct Hr.

(* The NULL arm: a0 = 0 -> errno := ENOMEM, a0 = 0 at the wrapper's return. *)
Lemma m_null : forall (regs : bvmap 5 word) (mem : word -> option byte) (sp vra vs0 vs1 vs2 vs3 vs4 vs5 w0 : Z),
bv_unsigned (getr regs 2) = sp -> TFIB_IMG_END + 16 <= sp -> sp + 2144 <= 2 ^ 64 ->
getr regs 10 = w64 0 -> getr regs 4 = w64 TFIB_TP ->
Forall (fun v => 0 <= v < 2 ^ 64) [vra; vs0; vs1; vs2; vs3; vs4; vs5; w0] ->
afr_okm mem sp w0 -> ifr_okm mem (sp + IFR_OFF) vra vs0 vs1 vs2 vs3 vs4 vs5 ->
(forall a, sp - 16 <= a < sp -> apresent H mem a) -> YK0s.ret_ok (w64 vra) ->
SRr tfibsegs W (mkCfg (mkst regs (w64 RA_ALLOC) mem (seg_rom tfibsegs)) md)
(ret_postm regs (MRerrm mem (sp - 16) sp) (sp + 2144) 0 vra vs0 vs1 vs2 vs3 vs4 vs5).
Proof.
intros regs mem sp vra vs0 vs1 vs2 vs3 vs4 vs5 w0 Hsp Hlo Hhi G10 G4 RV [A00 A0] (I0 & I1 & I2 & I3 & I4 & I5 & I6) HP Hret.
pose proof Hwx_tfa as Hwx. range7. unfold IFR_OFF in *. unfold TFIB_IMG_END in Hlo.
set (X := xvm vra vs0 vs1 vs2 vs3 vs4 vs5 w0).
assert (E2 : bv_unsigned (ew (Ereg regs X) 2) = sp) by (rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); exact Hsp).
assert (E4 : bv_unsigned (ew (Ereg regs X) 4) = TFIB_TP).
{ rewrite (ew_Ereg_nat regs _ 4 4%bv eq_refl), G4. unfold w64, TFIB_TP. apply unsigned_lit_small. lia. }
assert (HS0 : st_ok tfibsegs (Ereg regs X) SNm (restrict (w_H W) (mkst regs (Z_to_bv 64 RA_ALLOC) mem (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. unfold SNm. apply (entry_st_ok_full tfibsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]].
    + unfold region_ok, ESFm. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite E2.
      split; [lia|]. split; [lia|]. split; [intros o Ho; apply apresent_wr_m, HP; lia|]. apply Forall_nil.
    + unfold region_ok, AFRm. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite E2.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [apply (chunk8_atom_m regs X _ sp 0 7 w0); [reflexivity|lia|eapply val_mem_addr_m; [exact A00|lia]]|].
      apply Forall_cons; [apply chunk8_lit_m; [unfold RA_ASAN_MALLOC, tfib_A____interceptor_malloc; lia|eapply val_mem_addr_m; [exact A0|lia]]|]. apply Forall_nil.
    + unfold region_ok, IFRm. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite E2. unfold IFR_OFF.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      ifr_chunks regs X (mrestrict (w_H W) mem) sp 2088 vra vs0 vs1 vs2 vs3 vs4 vs5 I0 I1 I2 I3 I4 I5 I6.
    + unfold region_ok, ERRm. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite E4.
      unfold TFIB_TP. split; [lia|]. split; [lia|]. split; [intros o Ho; apply rw_wr_m; lia|]. apply Forall_nil.
  - cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint, ESFm, AFRm, IFRm, ERRm.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. unfold IFR_OFF. rewrite !E2, !E4. unfold TFIB_TP. repeat split; lia.
  - split; [exact I | split; exact I]. }
pose proof (st_ok_pin_reg (Ereg regs X) SNm _ 10%bv (SLit 0) HS0 ltac:(intros XX; discriminate XX)
  ltac:(cbn [restrict ms_regs mkst]; rewrite G10; reflexivity)) as HS. clear HS0.
change (w64 RA_ALLOC) with (Z_to_bv 64 RA_ALLOC).
srr_run_sh tfibtbl_rtA_ok HS.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => rename msx into msA end.
assert (MEQ : forall x : word, ~ (sp - 16 <= bv_unsigned x < sp) -> ~ (TFIB_ERRNO <= bv_unsigned x < TFIB_ERRNO + 4) -> ms_mem msA x = mem x).
{ intros x N1 N2. apply HF. intros Hw. destruct (in_wrange_windows _ _ _ Hw) as (b & lo & hi & Hin & Hrg). vm_compute in Hin.
  repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <- <-; cbn [base_val] in Hrg; rewrite ?E2, ?E4 in Hrg; unfold TFIB_ERRNO, TFIB_TP in *; lia|]).
  destruct Hin. }
clear HF HFr.
assert (V12 : val_mem tfibsegs (mrestrict (w_H W) (ms_mem msA)) TFIB_ERRNO 4 12).
{ pose proof (st_ok_chunk_val (w_H W) _ _ _ 3 _ 0 (-164) 4 (SLit 12) 12 HS eq_refl eq_refl eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as V.
  cbn [base_val YP09.r_base N.to_nat] in V. rewrite E4 in V. eapply val_mem_addr_m; [exact V | unfold TFIB_ERRNO, TFIB_TP; lia]. }
assert (PW : forall a, sp - 16 <= a < sp -> apresent (w_H W) (ms_mem msA) a).
{ intros a Ha. eapply (st_ok_window_apresent (w_H W) _ _ _ 0 _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite E2; lia | unfold TFIB_IMG_END; lia]. }
ret_regs HS E2 Hret msA vra.
split. { split; [exact MEQ|]. split; [exact V12|]. split; [exact PW|]. intros a Ha Hv. exact (vis_keep_m mem (ms_mem msA) _ _ a Ha MEQ V12 PW Hv). }
ret_tail HS E2.
split. { let R := fresh "R" in rreg HS (10%bv : bv 5) R; rewrite R; reflexivity. }
ret_keep HS.
Qed.

(* The block arm: a0 = v <> 0 -> a0 = v at the wrapper's return, memory unchanged. *)
Lemma m_blk : forall (regs : bvmap 5 word) (mem : word -> option byte) (sp v vra vs0 vs1 vs2 vs3 vs4 vs5 w0 : Z),
bv_unsigned (getr regs 2) = sp -> TFIB_IMG_END <= sp -> sp + 2144 <= 2 ^ 64 ->
getr regs 10 = w64 v -> 0 < v < 2 ^ 64 ->
Forall (fun v => 0 <= v < 2 ^ 64) [vra; vs0; vs1; vs2; vs3; vs4; vs5; w0] ->
afr_okm mem sp w0 -> ifr_okm mem (sp + IFR_OFF) vra vs0 vs1 vs2 vs3 vs4 vs5 -> YK0s.ret_ok (w64 vra) ->
SRr tfibsegs W (mkCfg (mkst regs (w64 RA_ALLOC) mem (seg_rom tfibsegs)) md)
(ret_postm regs (fun m' => forall x, m' x = mem x) (sp + 2144) v vra vs0 vs1 vs2 vs3 vs4 vs5).
Proof.
intros regs mem sp v vra vs0 vs1 vs2 vs3 vs4 vs5 w0 Hsp Hlo Hhi G10 Hv RV [A00 A0] (I0 & I1 & I2 & I3 & I4 & I5 & I6) Hret.
pose proof Hwx_tfa as Hwx. range7. unfold IFR_OFF in *. unfold TFIB_IMG_END in Hlo.
set (X := xvm vra vs0 vs1 vs2 vs3 vs4 vs5 w0).
assert (E2 : bv_unsigned (ew (Ereg regs X) 2) = sp) by (rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); exact Hsp).
assert (E10 : ew (Ereg regs X) 10 = w64 v) by (rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact G10).
assert (HS : st_ok tfibsegs (Ereg regs X) SBm (restrict (w_H W) (mkst regs (w64 RA_ALLOC) mem (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. unfold SBm. change (w64 RA_ALLOC) with (Z_to_bv 64 RA_ALLOC). apply (entry_st_ok_full tfibsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    + unfold region_ok, AFRm. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite E2.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [apply (chunk8_atom_m regs X _ sp 0 7 w0); [reflexivity|lia|eapply val_mem_addr_m; [exact A00|lia]]|].
      apply Forall_cons; [apply chunk8_lit_m; [unfold RA_ASAN_MALLOC, tfib_A____interceptor_malloc; lia|eapply val_mem_addr_m; [exact A0|lia]]|]. apply Forall_nil.
    + unfold region_ok, IFRm. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite E2. unfold IFR_OFF.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      ifr_chunks regs X (mrestrict (w_H W) mem) sp 2088 vra vs0 vs1 vs2 vs3 vs4 vs5 I0 I1 I2 I3 I4 I5 I6.
  - cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint, AFRm, IFRm.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. unfold IFR_OFF. rewrite !E2. repeat split; lia.
  - split; [exact I | split; exact I]. }
change (w64 RA_ALLOC) with (Z_to_bv 64 RA_ALLOC) in HS |- *.
assert (NOWR : forall (ma mb : word -> option byte), frame_of (Ereg regs X) (ss_mem SBm) ma mb -> forall x, mb x = ma x).
{ intros ma mb HFx x. apply HFx. intros Hw. destruct (in_wrange_windows _ _ _ Hw) as (b & lo & hi & Hin & Hrg). vm_compute in Hin.
  repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <- <-; cbn [fst snd] in Hrg; lia|]). destruct Hin. }
srr_run_sh tfibtbl_rtA_ok HS.
pose proof (NOWR _ _ HF) as MEQ1. clear HF HFr.
srr_branch_sh tfibtbl_rtA_ok HS.
- exfalso. rewrite branch_eq_U in Hc. rewrite !U_zev in Hc by reflexivity. cbn [zev] in Hc.
  unfold rho_of in Hc. rewrite E10 in Hc. unfold w64 in Hc. rewrite unsigned_lit_small in Hc by lia.
  rewrite ?Z.add_0_r in Hc. change (zcanon 0) with 0 in Hc. rewrite zcanon_id in Hc by (unfold M64; lia).
  apply Z.eqb_eq in Hc. lia.
- srr_run_sh tfibtbl_rtA_ok HS.
  lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => rename msx into msA end.
  assert (MEQ : forall x, ms_mem msA x = mem x) by (intros x; rewrite (NOWR _ _ HF x); apply MEQ1). clear HF HFr.
  ret_regs HS E2 Hret msA vra.
  split; [exact MEQ|].
  ret_tail HS E2.
  split. { let R := fresh "R" in rreg HS (10%bv : bv 5) R; rewrite R; exact E10. }
  ret_keep HS.
Qed.
End W.
End c.
