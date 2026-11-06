(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/WrapMallocARetM.v, with its module names and numbers changed; 235 of its 352 lines of code are new or changed and 115 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10-29: relocated from proofs/plugin-hostd/fuzz_reply/lib/A/RGthinM2.v (hub 66a127cb11e, blob 93b86654a578) to omx-clap-core/fuzz_preset's asan image A by a Theorem Labs lane's internal file alreloc.py (frozen-c4338d099cfb8025), module paths and every image numeral moved by symbol + offset; record, the internal file A5.md. *)
(* fuzz_preset.asan image A: the machine runs of the thin realloc segments that end at realloc's return (the epilogues of
   Reallocate, asan_realloc and the interceptor), see RGthinM.v for the provenance:
   - [m3]: Deallocate's return into Reallocate (0x330ec) -> realloc's return with a0 = the new block
     (YF78.v:437 succ_leaf's machine part);
   - [m4]: Allocate's return into Reallocate (0x33058) with NULL -> realloc's return with a0 = 0 and
     errno = ENOMEM through SetErrnoToENOMEM (YF68.v:104 c_null);
   - [m6]: Allocate's return into asan_realloc (its NULL-input call, 0x32fb8) -> realloc's return with a0 = the
     result, errno = ENOMEM on NULL.
   The frames are given relative to the sp at the start: Reallocate's 48 bytes (saved s4..s0, ra = 0x32fdc),
   asan_realloc's 16 (ra = 0x53ce4) and the interceptor's top 64 bytes (saved s6..s0 and ra = realloc's return
   pc). *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v AB1h AF0x.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import RGthinK RGthinM.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* The frame regions, based at atom 2 (the sp at the start).  Atoms 32..36: Reallocate's saved s4..s0; 37..44:
   the interceptor's saved ra, s0..s6. *)
Definition RFR (wlo whi : Z) : YP09.region := YP09.mkRegion (Some 2%nat) 0 48 wlo whi
[c8 0 (SOff 32 0); c8 8 (SOff 33 0); c8 16 (SOff 34 0); c8 24 (SOff 35 0); c8 32 (SOff 36 0); c8 40 (SLit RT_RA_R)].
Definition AFR (b : Z) : YP09.region := YP09.mkRegion (Some 2%nat) b (b + 16) 0 0 [c8 (b + 8) (SLit RT_RA_I)].
Definition IFR (b : Z) : YP09.region := YP09.mkRegion (Some 2%nat) b (b + 64) 0 0
[c8 b (SOff 44 0); c8 (b + 8) (SOff 43 0); c8 (b + 16) (SOff 42 0); c8 (b + 24) (SOff 41 0); c8 (b + 32) (SOff 40 0);
 c8 (b + 40) (SOff 39 0); c8 (b + 48) (SOff 38 0); c8 (b + 56) (SOff 37 0)].
Definition ERR : YP09.region := YP09.mkRegion (Some 4%nat) (-164) (-160) (-164) (-160) [].
Definition ESF : YP09.region := YP09.mkRegion (Some 2%nat) (-16) 0 (-16) 0 [].
Definition S3 : sstate := mkSS RT_RA_D sr_atoms [RFR 0 0; AFR 48; IFR 2144] None (mkFacts [(20%nat, mkAF 4096 (2 ^ 47) 0)] [] []).
Definition S4 : sstate := mkSS RT_RA_A sr_atoms [RFR 32 48; AFR 48; IFR 2144; ERR] None (mkFacts [] [] []).
Definition S6 : sstate := mkSS RT_RA_NA sr_atoms [ESF; AFR 0; IFR 2096; ERR] None (mkFacts [] [] []).

Definition xvals (w0 w1 w2 w3 w4 vra vs0 vs1 vs2 vs3 vs4 vs5 vs6 : Z) : list word :=
[w64 w0; w64 w1; w64 w2; w64 w3; w64 w4; w64 vra; w64 vs0; w64 vs1; w64 vs2; w64 vs3; w64 vs4; w64 vs5; w64 vs6].

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma chunk8_atom : forall regs (extra : list word) m base off j v,
nth j extra (Z_to_bv 64 0) = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> val_mem tfibsegs m (base + off) 8 v ->
YP09.chunk_ok tfibsegs (Ereg regs extra) m base (c8 off (SOff (32 + j) 0)).
Proof.
intros regs extra m base off j v Hn Hv Hm. apply (chunk_ok_val tfibsegs _ m base off 8 (SOff (32 + j) 0) v); [|cbn; lia|cbn; lia|exact Hm].
cbn [sv_denot]. rewrite ew_Ereg_extra, Hn. rewrite unsigned_lit_small by lia. f_equal; lia.
Qed.
Lemma chunk8_lit : forall E m base off v, 0 <= v < 2 ^ 64 -> val_mem tfibsegs m (base + off) 8 v ->
YP09.chunk_ok tfibsegs E m base (c8 off (SLit v)).
Proof. intros E m base off v Hv Hm. apply (chunk_ok_val tfibsegs E m base off 8 (SLit v) v); [reflexivity|cbn; lia|cbn; lia|exact Hm]. Qed.
Lemma vm_vis : forall (H : word -> bool) mem a (w : nat) v i, val_mem tfibsegs (mrestrict H mem) a w v -> 0 <= i < Z.of_nat w ->
aview tfibsegs H mem (a + i) <> None.
Proof.
intros H mem a w v i Hv Hi. unfold aview. replace i with (Z.of_nat (Z.to_nat i)) by lia. rewrite (Hv (Z.to_nat i) ltac:(lia)). discriminate.
Qed.

Section W.
Variable W : world tfibsegs.
Variable md : Model.
Local Notation H := (w_H W).

Definition rfr_ok (m : word -> option byte) (a w0 w1 w2 w3 w4 : Z) : Prop :=
val_mem tfibsegs (mrestrict H m) a 8 w0 /\ val_mem tfibsegs (mrestrict H m) (a + 8) 8 w1 /\
val_mem tfibsegs (mrestrict H m) (a + 16) 8 w2 /\ val_mem tfibsegs (mrestrict H m) (a + 24) 8 w3 /\
val_mem tfibsegs (mrestrict H m) (a + 32) 8 w4 /\ val_mem tfibsegs (mrestrict H m) (a + 40) 8 RT_RA_R.
Definition afr_ok (m : word -> option byte) (a : Z) : Prop := val_mem tfibsegs (mrestrict H m) (a + 8) 8 RT_RA_I.
Definition ifr_ok (m : word -> option byte) (a vra vs0 vs1 vs2 vs3 vs4 vs5 vs6 : Z) : Prop :=
val_mem tfibsegs (mrestrict H m) (a + 56) 8 vra /\ val_mem tfibsegs (mrestrict H m) (a + 48) 8 vs0 /\
val_mem tfibsegs (mrestrict H m) (a + 40) 8 vs1 /\ val_mem tfibsegs (mrestrict H m) (a + 32) 8 vs2 /\
val_mem tfibsegs (mrestrict H m) (a + 24) 8 vs3 /\ val_mem tfibsegs (mrestrict H m) (a + 16) 8 vs4 /\
val_mem tfibsegs (mrestrict H m) (a + 8) 8 vs5 /\ val_mem tfibsegs (mrestrict H m) a 8 vs6.

(* realloc's return: the interceptor's callee-saved registers restored from its frame, a0 = [a0], memory [MR]. *)
Definition ret_post (regs : bvmap 5 word) (MR : (word -> option byte) -> Prop) (sp' a0 vra vs0 vs1 vs2 vs3 vs4 vs5 vs6 : Z)
(W' : world tfibsegs) (c' : config) : Prop :=
W' = W /\ exists regs' mem' mat,
c' = mkCfg (mkst regs' (w64 vra) mem' (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md) mat md) /\ MR mem' /\
getr regs' 2 = w64 sp' /\ getr regs' 1 = w64 vra /\ getr regs' 8 = w64 vs0 /\ getr regs' 9 = w64 vs1 /\
getr regs' 18 = w64 vs2 /\ getr regs' 19 = w64 vs3 /\ getr regs' 20 = w64 vs4 /\ getr regs' 21 = w64 vs5 /\
getr regs' 22 = w64 vs6 /\ getr regs' 10 = w64 a0 /\
(forall r : bv 5, In r [3; 4; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr regs r).

Ltac reg_ent HS r k :=
let R := fresh "R" in rreg HS r R; rewrite R; exact (ew_Ereg_nat _ _ k r eq_refl).
Ltac reg_x HS r j :=
let R := fresh "R" in rreg HS r R; rewrite R; exact (ew_Ereg_extra _ _ j).
Ltac range8 := match goal with RV : Forall _ _ |- _ =>
  repeat (apply Forall_cons_iff in RV as [? RV]) end.

Ltac ifr_chunks regs X m sp b vra vs0 vs1 vs2 vs3 vs4 vs5 vs6 I0 I1 I2 I3 I4 I5 I6 I7 :=
  apply Forall_cons; [apply (chunk8_atom regs X m sp b 12 vs6); [reflexivity|lia|eapply val_mem_addr; [exact I7|lia]]|];
  apply Forall_cons; [apply (chunk8_atom regs X m sp (b + 8) 11 vs5); [reflexivity|lia|eapply val_mem_addr; [exact I6|lia]]|];
  apply Forall_cons; [apply (chunk8_atom regs X m sp (b + 16) 10 vs4); [reflexivity|lia|eapply val_mem_addr; [exact I5|lia]]|];
  apply Forall_cons; [apply (chunk8_atom regs X m sp (b + 24) 9 vs3); [reflexivity|lia|eapply val_mem_addr; [exact I4|lia]]|];
  apply Forall_cons; [apply (chunk8_atom regs X m sp (b + 32) 8 vs2); [reflexivity|lia|eapply val_mem_addr; [exact I3|lia]]|];
  apply Forall_cons; [apply (chunk8_atom regs X m sp (b + 40) 7 vs1); [reflexivity|lia|eapply val_mem_addr; [exact I2|lia]]|];
  apply Forall_cons; [apply (chunk8_atom regs X m sp (b + 48) 6 vs0); [reflexivity|lia|eapply val_mem_addr; [exact I1|lia]]|];
  apply Forall_cons; [apply (chunk8_atom regs X m sp (b + 56) 5 vra); [reflexivity|lia|eapply val_mem_addr; [exact I0|lia]]|];
  apply Forall_nil.

Lemma m3 : forall (regs : bvmap 5 word) (mem : word -> option byte) (sp qa w0 w1 w2 w3 w4 vra vs0 vs1 vs2 vs3 vs4 vs5 vs6 : Z),
bv_unsigned (getr regs 2) = sp -> 0x600000 <= sp -> sp + 2208 <= 2 ^ 64 ->
getr regs 20 = w64 qa -> 4096 <= qa <= 2 ^ 47 ->
Forall (fun v => 0 <= v < 2 ^ 64) [w0; w1; w2; w3; w4; vra; vs0; vs1; vs2; vs3; vs4; vs5; vs6] ->
rfr_ok mem sp w0 w1 w2 w3 w4 -> afr_ok mem (sp + 48) -> ifr_ok mem (sp + 2144) vra vs0 vs1 vs2 vs3 vs4 vs5 vs6 ->
YK0s.ret_ok (w64 vra) ->
SRr tfibsegs W (mkCfg (mkst regs (w64 RT_RA_D) mem (seg_rom tfibsegs)) md)
(ret_post regs (fun m' => forall x, m' x = mem x) (sp + 2208) qa vra vs0 vs1 vs2 vs3 vs4 vs5 vs6).
Proof.
intros regs mem sp qa w0 w1 w2 w3 w4 vra vs0 vs1 vs2 vs3 vs4 vs5 vs6 Hsp Hlo Hhi G20 Hq RV
(F0 & F1 & F2 & F3 & F4 & F5) A0 (I0 & I1 & I2 & I3 & I4 & I5 & I6 & I7) Hret.
pose proof Hwx_tfa as Hwx. range8.
set (X := xvals w0 w1 w2 w3 w4 vra vs0 vs1 vs2 vs3 vs4 vs5 vs6).
assert (E2 : bv_unsigned (ew (Ereg regs X) 2) = sp) by (rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); exact Hsp).
assert (E20 : ew (Ereg regs X) 20 = w64 qa) by (rewrite (ew_Ereg_nat regs _ 20 20%bv eq_refl); exact G20).
assert (HS : st_ok tfibsegs (Ereg regs X) S3 (restrict (w_H W) (mkst regs (w64 RT_RA_D) mem (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. unfold S3. change (w64 RT_RA_D) with (Z_to_bv 64 RT_RA_D). apply (entry_st_ok_full tfibsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
    + unfold region_ok, RFR. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite E2.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [apply (chunk8_atom regs X _ sp 0 0 w0); [reflexivity|lia|eapply val_mem_addr; [exact F0|lia]]|].
      apply Forall_cons; [apply (chunk8_atom regs X _ sp 8 1 w1); [reflexivity|lia|eapply val_mem_addr; [exact F1|lia]]|].
      apply Forall_cons; [apply (chunk8_atom regs X _ sp 16 2 w2); [reflexivity|lia|eapply val_mem_addr; [exact F2|lia]]|].
      apply Forall_cons; [apply (chunk8_atom regs X _ sp 24 3 w3); [reflexivity|lia|eapply val_mem_addr; [exact F3|lia]]|].
      apply Forall_cons; [apply (chunk8_atom regs X _ sp 32 4 w4); [reflexivity|lia|eapply val_mem_addr; [exact F4|lia]]|].
      apply Forall_cons; [apply chunk8_lit; [unfold RT_RA_R; lia|eapply val_mem_addr; [exact F5|lia]]|]. apply Forall_nil.
    + unfold region_ok, AFR. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite E2.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [apply chunk8_lit; [unfold RT_RA_I; lia|eapply val_mem_addr; [exact A0|lia]]|]. apply Forall_nil.
    + unfold region_ok, IFR. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite E2.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      ifr_chunks regs X (mrestrict (w_H W) mem) sp 2144 vra vs0 vs1 vs2 vs3 vs4 vs5 vs6 I0 I1 I2 I3 I4 I5 I6 I7.
  - cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint, RFR, AFR, IFR.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite !E2. repeat split; lia.
  - split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok; cbn [af_lo af_hi af_al2].
    rewrite E20. unfold w64. rewrite !unsigned_lit_small by lia.
    split; [split; [lia | split; [rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | lia]]|]. exact I. }
change (w64 RT_RA_D) with (Z_to_bv 64 RT_RA_D) in HS |- *.
srr_run_sh rt_tbl_ok HS.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => rename msx into msA end.
assert (MEQ : forall x, ms_mem msA x = mem x).
{ intros x. apply HF. intros Hw. destruct (in_wrange_windows _ _ _ Hw) as (b & lo & hi & Hin & Hrg). vm_compute in Hin.
  repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <- <-; cbn [fst snd] in Hrg; lia|]). destruct Hin. }
clear HF HFr.
eapply (SRr_ret_at tfibsegs rt_tbl rt_tbl_ok Hwx W _); [exact HS | reflexivity | vm_compute; reflexivity |].
intros mat'. split; [reflexivity|].
assert (R1 : getr (ms_regs msA) 1 = w64 vra) by reg_x HS (1%bv : bv 5) 5%nat.
exists (ms_regs msA), (ms_mem msA), mat'.
split. { rewrite R1. unfold YK0s.ret_ok in Hret. rewrite Hret. reflexivity. }
split; [exact MEQ|].
split. { let R := fresh "R" in rreg HS (2%bv : bv 5) R; rewrite R, E2; reflexivity. }
split; [exact R1|].
split; [reg_x HS (8%bv : bv 5) 6%nat|]. split; [reg_x HS (9%bv : bv 5) 7%nat|]. split; [reg_x HS (18%bv : bv 5) 8%nat|].
split; [reg_x HS (19%bv : bv 5) 9%nat|]. split; [reg_x HS (20%bv : bv 5) 10%nat|]. split; [reg_x HS (21%bv : bv 5) 11%nat|].
split; [reg_x HS (22%bv : bv 5) 12%nat|].
split. { let R := fresh "R" in rreg HS (10%bv : bv 5) R; rewrite R; exact E20. }
intros r Hr. cbn [In] in Hr.
repeat (destruct Hr as [<-|Hr]; [ lazymatch goal with |- getr _ ?rr = _ =>
  let k := eval vm_compute in (Z.to_nat (bv_unsigned rr)) in reg_ent HS rr k end |]).
destruct Hr.
Qed.

(* The memory at realloc's return on the ENOMEM paths: changed only in a stack window [lo, hi) and errno; errno
   holds 12; the window stays present; every visible byte stays visible. *)
Definition MRerr (mem : word -> option byte) (lo hi : Z) (m' : word -> option byte) : Prop :=
(forall x : word, ~ (lo <= bv_unsigned x < hi) -> ~ (RT_ERRNO <= bv_unsigned x < RT_ERRNO + 4) -> m' x = mem x) /\
val_mem tfibsegs (mrestrict H m') RT_ERRNO 4 12 /\ (forall a, lo <= a < hi -> apresent H m' a) /\
(forall a, 0 <= a < 2 ^ 64 -> aview tfibsegs H mem a <> None -> aview tfibsegs H m' a <> None).

Lemma vis_keep : forall (mem m' : word -> option byte) lo hi a, 0 <= a < 2 ^ 64 ->
(forall x : word, ~ (lo <= bv_unsigned x < hi) -> ~ (RT_ERRNO <= bv_unsigned x < RT_ERRNO + 4) -> m' x = mem x) ->
val_mem tfibsegs (mrestrict H m') RT_ERRNO 4 12 -> (forall a, lo <= a < hi -> apresent H m' a) ->
aview tfibsegs H mem a <> None -> aview tfibsegs H m' a <> None.
Proof.
intros mem m' lo hi a Ha MEQ V P Hv.
destruct (Z_lt_le_dec a lo) as [L1|L1]; [|destruct (Z_lt_le_dec a hi) as [L2|L2]].
3: destruct (Z_lt_le_dec a RT_ERRNO) as [L3|L3]; [|destruct (Z_lt_le_dec a (RT_ERRNO + 4)) as [L4|L4]].
- destruct (Z_lt_le_dec a RT_ERRNO) as [L3|L3]; [|destruct (Z_lt_le_dec a (RT_ERRNO + 4)) as [L4|L4]].
  + rewrite (aview_same H mem m' a). exact Hv. apply MEQ; rewrite unsigned_lit_small by lia; lia.
  + replace a with (RT_ERRNO + (a - RT_ERRNO)) by lia. apply (vm_vis H m' RT_ERRNO 4 12); [exact V | cbn; lia].
  + rewrite (aview_same H mem m' a). exact Hv. apply MEQ; rewrite unsigned_lit_small by lia; lia.
- destruct (P a ltac:(lia)) as [Hh [b Hb]]. unfold aview, mbyte, mrestrict. rewrite Hh, Hb. discriminate.
- rewrite (aview_same H mem m' a). exact Hv. apply MEQ; rewrite unsigned_lit_small by lia; lia.
- replace a with (RT_ERRNO + (a - RT_ERRNO)) by lia. apply (vm_vis H m' RT_ERRNO 4 12); [exact V | cbn; lia].
- rewrite (aview_same H mem m' a). exact Hv. apply MEQ; rewrite unsigned_lit_small by lia; lia.
Qed.

Ltac ret_regs HS E2 Hret msA vra :=
  eapply (SRr_ret_at tfibsegs rt_tbl rt_tbl_ok ltac:(assumption) W _); [exact HS | reflexivity | vm_compute; reflexivity |];
  let mat' := fresh "mat" in intros mat'; split; [reflexivity|];
  let R1 := fresh "R1" in assert (R1 : getr (ms_regs msA) 1 = w64 vra) by reg_x HS (1%bv : bv 5) 5%nat;
  exists (ms_regs msA), (ms_mem msA), mat';
  split; [rewrite R1; unfold YK0s.ret_ok in Hret; rewrite Hret; reflexivity|].
Ltac ret_tail HS E2 :=
  split; [let R := fresh "R" in rreg HS (2%bv : bv 5) R; rewrite R, E2; reflexivity|];
  split; [assumption|];
  split; [reg_x HS (8%bv : bv 5) 6%nat|]; split; [reg_x HS (9%bv : bv 5) 7%nat|]; split; [reg_x HS (18%bv : bv 5) 8%nat|];
  split; [reg_x HS (19%bv : bv 5) 9%nat|]; split; [reg_x HS (20%bv : bv 5) 10%nat|]; split; [reg_x HS (21%bv : bv 5) 11%nat|];
  split; [reg_x HS (22%bv : bv 5) 12%nat|].
Ltac ret_keep HS :=
  let r := fresh "r" in let Hr := fresh "Hr" in intros r Hr; cbn [In] in Hr;
  repeat (destruct Hr as [<-|Hr]; [ lazymatch goal with |- getr _ ?rr = _ =>
    let k := eval vm_compute in (Z.to_nat (bv_unsigned rr)) in reg_ent HS rr k end |]);
  destruct Hr.

Lemma m4 : forall (regs : bvmap 5 word) (mem : word -> option byte) (sp w0 w1 w2 w3 w4 vra vs0 vs1 vs2 vs3 vs4 vs5 vs6 : Z),
bv_unsigned (getr regs 2) = sp -> 0x600000 <= sp -> sp + 2208 <= 2 ^ 64 ->
getr regs 10 = w64 0 -> getr regs 4 = w64 RT_TP ->
Forall (fun v => 0 <= v < 2 ^ 64) [w0; w1; w2; w3; w4; vra; vs0; vs1; vs2; vs3; vs4; vs5; vs6] ->
rfr_ok mem sp w0 w1 w2 w3 w4 -> afr_ok mem (sp + 48) -> ifr_ok mem (sp + 2144) vra vs0 vs1 vs2 vs3 vs4 vs5 vs6 ->
(forall a, sp + 32 <= a < sp + 48 -> apresent H mem a) -> YK0s.ret_ok (w64 vra) ->
SRr tfibsegs W (mkCfg (mkst regs (w64 RT_RA_A) mem (seg_rom tfibsegs)) md)
(ret_post regs (MRerr mem (sp + 32) (sp + 48)) (sp + 2208) 0 vra vs0 vs1 vs2 vs3 vs4 vs5 vs6).
Proof.
intros regs mem sp w0 w1 w2 w3 w4 vra vs0 vs1 vs2 vs3 vs4 vs5 vs6 Hsp Hlo Hhi G10 G4 RV
(F0 & F1 & F2 & F3 & F4 & F5) A0 (I0 & I1 & I2 & I3 & I4 & I5 & I6 & I7) HP Hret.
pose proof Hwx_tfa as Hwx. range8.
set (X := xvals w0 w1 w2 w3 w4 vra vs0 vs1 vs2 vs3 vs4 vs5 vs6).
assert (E2 : bv_unsigned (ew (Ereg regs X) 2) = sp) by (rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); exact Hsp).
assert (E4 : bv_unsigned (ew (Ereg regs X) 4) = RT_TP).
{ rewrite (ew_Ereg_nat regs _ 4 4%bv eq_refl), G4. unfold w64, RT_TP. apply unsigned_lit_small. lia. }
assert (HS0 : st_ok tfibsegs (Ereg regs X) S4 (restrict (w_H W) (mkst regs (Z_to_bv 64 RT_RA_A) mem (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. unfold S4. apply (entry_st_ok_full tfibsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]].
    + unfold region_ok, RFR. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite E2.
      split; [lia|]. split; [lia|]. split; [intros o Ho; apply apresent_wr, HP; lia|].
      apply Forall_cons; [apply (chunk8_atom regs X _ sp 0 0 w0); [reflexivity|lia|eapply val_mem_addr; [exact F0|lia]]|].
      apply Forall_cons; [apply (chunk8_atom regs X _ sp 8 1 w1); [reflexivity|lia|eapply val_mem_addr; [exact F1|lia]]|].
      apply Forall_cons; [apply (chunk8_atom regs X _ sp 16 2 w2); [reflexivity|lia|eapply val_mem_addr; [exact F2|lia]]|].
      apply Forall_cons; [apply (chunk8_atom regs X _ sp 24 3 w3); [reflexivity|lia|eapply val_mem_addr; [exact F3|lia]]|].
      apply Forall_cons; [apply (chunk8_atom regs X _ sp 32 4 w4); [reflexivity|lia|eapply val_mem_addr; [exact F4|lia]]|].
      apply Forall_cons; [apply chunk8_lit; [unfold RT_RA_R; lia|eapply val_mem_addr; [exact F5|lia]]|]. apply Forall_nil.
    + unfold region_ok, AFR. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite E2.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [apply chunk8_lit; [unfold RT_RA_I; lia|eapply val_mem_addr; [exact A0|lia]]|]. apply Forall_nil.
    + unfold region_ok, IFR. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite E2.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      ifr_chunks regs X (mrestrict (w_H W) mem) sp 2144 vra vs0 vs1 vs2 vs3 vs4 vs5 vs6 I0 I1 I2 I3 I4 I5 I6 I7.
    + unfold region_ok, ERR. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite E4.
      unfold RT_TP. split; [lia|]. split; [lia|]. split; [intros o Ho; apply rw_wr; lia|]. apply Forall_nil.
  - cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint, RFR, AFR, IFR, ERR.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite !E2, !E4. unfold RT_TP. repeat split; lia.
  - split; [exact I | split; exact I]. }
pose proof (st_ok_pin_reg (Ereg regs X) S4 _ 10%bv (SLit 0) HS0 ltac:(intros XX; discriminate XX)
  ltac:(cbn [restrict ms_regs mkst]; rewrite G10; reflexivity)) as HS. clear HS0.
change (w64 RT_RA_A) with (Z_to_bv 64 RT_RA_A).
srr_run_sh rt_tbl_ok HS.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => rename msx into msA end.
assert (MEQ : forall x : word, ~ (sp + 32 <= bv_unsigned x < sp + 48) -> ~ (RT_ERRNO <= bv_unsigned x < RT_ERRNO + 4) -> ms_mem msA x = mem x).
{ intros x N1 N2. apply HF. intros Hw. destruct (in_wrange_windows _ _ _ Hw) as (b & lo & hi & Hin & Hrg). vm_compute in Hin.
  repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <- <-; cbn [base_val] in Hrg; rewrite ?E2, ?E4 in Hrg; unfold RT_ERRNO, RT_TP in *; lia|]).
  destruct Hin. }
clear HF HFr.
assert (V12 : val_mem tfibsegs (mrestrict (w_H W) (ms_mem msA)) RT_ERRNO 4 12).
{ pose proof (st_ok_chunk_val (w_H W) _ _ _ 3 _ 0 (-164) 4 (SLit 12) 12 HS eq_refl eq_refl eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as V.
  cbn [base_val YP09.r_base N.to_nat] in V. rewrite E4 in V. eapply val_mem_addr; [exact V | unfold RT_ERRNO, RT_TP; lia]. }
assert (PW : forall a, sp + 32 <= a < sp + 48 -> apresent (w_H W) (ms_mem msA) a).
{ intros a Ha. eapply (st_ok_window_apresent (w_H W) _ _ _ 0 _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite E2; lia | unfold TFIB_IMG_END; lia]. }
ret_regs HS E2 Hret msA vra.
split. { split; [exact MEQ|]. split; [exact V12|]. split; [exact PW|]. intros a Ha Hv. exact (vis_keep mem (ms_mem msA) _ _ a Ha MEQ V12 PW Hv). }
ret_tail HS E2.
split. { let R := fresh "R" in rreg HS (10%bv : bv 5) R; rewrite R; reflexivity. }
ret_keep HS.
Qed.

Lemma m6b : forall (regs : bvmap 5 word) (mem : word -> option byte) (sp vra vs0 vs1 vs2 vs3 vs4 vs5 vs6 : Z),
bv_unsigned (getr regs 2) = sp -> 0x600000 + 16 <= sp -> sp + 2160 <= 2 ^ 64 ->
getr regs 10 = w64 0 -> getr regs 4 = w64 RT_TP ->
Forall (fun v => 0 <= v < 2 ^ 64) [0; 0; 0; 0; 0; vra; vs0; vs1; vs2; vs3; vs4; vs5; vs6] ->
afr_ok mem sp -> ifr_ok mem (sp + 2096) vra vs0 vs1 vs2 vs3 vs4 vs5 vs6 ->
(forall a, sp - 16 <= a < sp -> apresent H mem a) -> YK0s.ret_ok (w64 vra) ->
SRr tfibsegs W (mkCfg (mkst regs (w64 RT_RA_NA) mem (seg_rom tfibsegs)) md)
(ret_post regs (MRerr mem (sp - 16) sp) (sp + 2160) 0 vra vs0 vs1 vs2 vs3 vs4 vs5 vs6).
Proof.
intros regs mem sp vra vs0 vs1 vs2 vs3 vs4 vs5 vs6 Hsp Hlo Hhi G10 G4 RV A0 (I0 & I1 & I2 & I3 & I4 & I5 & I6 & I7) HP Hret.
pose proof Hwx_tfa as Hwx. range8.
set (X := xvals 0 0 0 0 0 vra vs0 vs1 vs2 vs3 vs4 vs5 vs6).
assert (E2 : bv_unsigned (ew (Ereg regs X) 2) = sp) by (rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); exact Hsp).
assert (E4 : bv_unsigned (ew (Ereg regs X) 4) = RT_TP).
{ rewrite (ew_Ereg_nat regs _ 4 4%bv eq_refl), G4. unfold w64, RT_TP. apply unsigned_lit_small. lia. }
assert (HS0 : st_ok tfibsegs (Ereg regs X) S6 (restrict (w_H W) (mkst regs (Z_to_bv 64 RT_RA_NA) mem (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. unfold S6. apply (entry_st_ok_full tfibsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]].
    + unfold region_ok, ESF. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite E2.
      split; [lia|]. split; [lia|]. split; [intros o Ho; apply apresent_wr, HP; lia|]. apply Forall_nil.
    + unfold region_ok, AFR. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite E2.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [apply chunk8_lit; [unfold RT_RA_I; lia|eapply val_mem_addr; [exact A0|lia]]|]. apply Forall_nil.
    + unfold region_ok, IFR. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite E2.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      ifr_chunks regs X (mrestrict (w_H W) mem) sp 2096 vra vs0 vs1 vs2 vs3 vs4 vs5 vs6 I0 I1 I2 I3 I4 I5 I6 I7.
    + unfold region_ok, ERR. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite E4.
      unfold RT_TP. split; [lia|]. split; [lia|]. split; [intros o Ho; apply rw_wr; lia|]. apply Forall_nil.
  - cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint, ESF, AFR, IFR, ERR.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite !E2, !E4. unfold RT_TP. repeat split; lia.
  - split; [exact I | split; exact I]. }
pose proof (st_ok_pin_reg (Ereg regs X) S6 _ 10%bv (SLit 0) HS0 ltac:(intros XX; discriminate XX)
  ltac:(cbn [restrict ms_regs mkst]; rewrite G10; reflexivity)) as HS. clear HS0.
change (w64 RT_RA_NA) with (Z_to_bv 64 RT_RA_NA).
srr_run_sh rt_tbl_ok HS.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => rename msx into msA end.
assert (MEQ : forall x : word, ~ (sp - 16 <= bv_unsigned x < sp) -> ~ (RT_ERRNO <= bv_unsigned x < RT_ERRNO + 4) -> ms_mem msA x = mem x).
{ intros x N1 N2. apply HF. intros Hw. destruct (in_wrange_windows _ _ _ Hw) as (b & lo & hi & Hin & Hrg). vm_compute in Hin.
  repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <- <-; cbn [base_val] in Hrg; rewrite ?E2, ?E4 in Hrg; unfold RT_ERRNO, RT_TP in *; lia|]).
  destruct Hin. }
clear HF HFr.
assert (V12 : val_mem tfibsegs (mrestrict (w_H W) (ms_mem msA)) RT_ERRNO 4 12).
{ pose proof (st_ok_chunk_val (w_H W) _ _ _ 3 _ 0 (-164) 4 (SLit 12) 12 HS eq_refl eq_refl eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as V.
  cbn [base_val YP09.r_base N.to_nat] in V. rewrite E4 in V. eapply val_mem_addr; [exact V | unfold RT_ERRNO, RT_TP; lia]. }
assert (PW : forall a, sp - 16 <= a < sp -> apresent (w_H W) (ms_mem msA) a).
{ intros a Ha. eapply (st_ok_window_apresent (w_H W) _ _ _ 0 _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite E2; lia | unfold TFIB_IMG_END; lia]. }
ret_regs HS E2 Hret msA vra.
split. { split; [exact MEQ|]. split; [exact V12|]. split; [exact PW|]. intros a Ha Hv. exact (vis_keep mem (ms_mem msA) _ _ a Ha MEQ V12 PW Hv). }
ret_tail HS E2.
split. { let R := fresh "R" in rreg HS (10%bv : bv 5) R; rewrite R; reflexivity. }
ret_keep HS.
Qed.

Definition S6A : sstate := mkSS RT_RA_NA sr_atoms [AFR 0; IFR 2096] None (mkFacts [] [] []).
Lemma m6a : forall (regs : bvmap 5 word) (mem : word -> option byte) (sp v vra vs0 vs1 vs2 vs3 vs4 vs5 vs6 : Z),
bv_unsigned (getr regs 2) = sp -> 0x600000 <= sp -> sp + 2160 <= 2 ^ 64 ->
getr regs 10 = w64 v -> 0 < v < 2 ^ 64 ->
Forall (fun v => 0 <= v < 2 ^ 64) [0; 0; 0; 0; 0; vra; vs0; vs1; vs2; vs3; vs4; vs5; vs6] ->
afr_ok mem sp -> ifr_ok mem (sp + 2096) vra vs0 vs1 vs2 vs3 vs4 vs5 vs6 -> YK0s.ret_ok (w64 vra) ->
SRr tfibsegs W (mkCfg (mkst regs (w64 RT_RA_NA) mem (seg_rom tfibsegs)) md)
(ret_post regs (fun m' => forall x, m' x = mem x) (sp + 2160) v vra vs0 vs1 vs2 vs3 vs4 vs5 vs6).
Proof.
intros regs mem sp v vra vs0 vs1 vs2 vs3 vs4 vs5 vs6 Hsp Hlo Hhi G10 Hv RV A0 (I0 & I1 & I2 & I3 & I4 & I5 & I6 & I7) Hret.
pose proof Hwx_tfa as Hwx. range8.
set (X := xvals 0 0 0 0 0 vra vs0 vs1 vs2 vs3 vs4 vs5 vs6).
assert (E2 : bv_unsigned (ew (Ereg regs X) 2) = sp) by (rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); exact Hsp).
assert (E10 : ew (Ereg regs X) 10 = w64 v) by (rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact G10).
assert (HS : st_ok tfibsegs (Ereg regs X) S6A (restrict (w_H W) (mkst regs (w64 RT_RA_NA) mem (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. unfold S6A. change (w64 RT_RA_NA) with (Z_to_bv 64 RT_RA_NA). apply (entry_st_ok_full tfibsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    + unfold region_ok, AFR. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite E2.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [apply chunk8_lit; [unfold RT_RA_I; lia|eapply val_mem_addr; [exact A0|lia]]|]. apply Forall_nil.
    + unfold region_ok, IFR. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite E2.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      ifr_chunks regs X (mrestrict (w_H W) mem) sp 2096 vra vs0 vs1 vs2 vs3 vs4 vs5 vs6 I0 I1 I2 I3 I4 I5 I6 I7.
  - cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint, AFR, IFR.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite !E2. repeat split; lia.
  - split; [exact I | split; exact I]. }
change (w64 RT_RA_NA) with (Z_to_bv 64 RT_RA_NA) in HS |- *.
assert (NOWR : forall (ma mb : word -> option byte), frame_of (Ereg regs X) (ss_mem S6A) ma mb -> forall x, mb x = ma x).
{ intros ma mb HFx x. apply HFx. intros Hw. destruct (in_wrange_windows _ _ _ Hw) as (b & lo & hi & Hin & Hrg). vm_compute in Hin.
  repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <- <-; cbn [fst snd] in Hrg; lia|]). destruct Hin. }
srr_run_sh rt_tbl_ok HS.
pose proof (NOWR _ _ HF) as MEQ1. clear HF HFr.
srr_branch_sh rt_tbl_ok HS.
- srr_run_sh rt_tbl_ok HS.
  lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => rename msx into msA end.
  assert (MEQ : forall x, ms_mem msA x = mem x) by (intros x; rewrite (NOWR _ _ HF x); apply MEQ1). clear HF HFr.
  ret_regs HS E2 Hret msA vra.
  split; [exact MEQ|].
  ret_tail HS E2.
  split. { let R := fresh "R" in rreg HS (10%bv : bv 5) R; rewrite R; exact E10. }
  ret_keep HS.
- exfalso. rewrite branch_ne_U in Hc. rewrite !U_zev in Hc by reflexivity. cbn [zev] in Hc.
  unfold rho_of in Hc. rewrite E10 in Hc. unfold w64 in Hc. rewrite unsigned_lit_small in Hc by lia.
  rewrite Z.add_0_r in Hc. change (zcanon 0) with 0 in Hc. rewrite zcanon_id in Hc by (unfold M64; lia).
  apply Bool.negb_false_iff, Z.eqb_eq in Hc. lia.
Qed.
End W.
End c.
