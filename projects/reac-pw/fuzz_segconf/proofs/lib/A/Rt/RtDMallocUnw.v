(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AFl0.v, AFl2.v, AFl3.v and AFl4.v (as relocated to plugin-hostd/fuzz_command): the unwinder call spec of the malloc chain with its post as one definition, and the walk of BufferedStackTrace::UnwindImpl 0x603d8 in the case cgif's spec leaves out, a frame pointer at or below the stack bottom, where UnwindFast stops at its check 0x78f34 with the one frame pc0. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/plugin-hostd/fuzz_command/lib/A/Rt/RtDMallocUnw.v (donor image sha256 c0661b96b5bd), with its module paths changed and its addresses moved to reac-pw/fuzz_segconf's ASan build. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.

From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.

From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI04 YO0d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A Require Import AB1v AB1q AF0l AF0m AF0x.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Definition DM_UNW_PC : Z := 0x5eb14.
Definition DM_UNW_STK : Z := 144.
Definition DM_BST : Z := 2064.
Definition DM_UNW_RET : Z := 0x5ec60.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* The unwinder's post with the trace it records as a parameter. *)
Definition dm_unw_post (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
(this bp : Z) (tr : list Z) : world tfibsegs -> config -> Prop :=
fun W' c' => W' = W /\ exists regs' mem' mat,
c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md) mat md) /\
regs_preserved regs regs' /\
(forall x : word, ~ (bv_unsigned (getr regs 2) - DM_UNW_STK <= bv_unsigned x < bv_unsigned (getr regs 2)) ->
~ (this + 8 <= bv_unsigned x < this + 12) ->
~ (this + 16 <= bv_unsigned x < this + 16 + 8 * 30) -> ~ (this + 2056 <= bv_unsigned x < this + DM_BST) ->
mem' x = mem x) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a) /\
val_mem tfibsegs (mrestrict (w_H W) mem') (this + 8) 4 (Z.of_nat (length tr)) /\
(forall i, (i < length tr)%nat -> val_mem tfibsegs (mrestrict (w_H W) mem') (this + 16 + 8 * Z.of_nat i) 8 (nth i tr 0)) /\
val_mem tfibsegs (mrestrict (w_H W) mem') (this + 2056) 8 bp.

(* cgif's spec of the unwinder call (lib/A/AFl0.v tfib_unwind_spec, the text this image's relocated chain states
   at A_UnwindImpl = 0x603d8, UNW_STK = 144, BST_SIZE = 2064); the chain proves it (AFl4.v tfib_unwind_ok), so
   it is discharged by conversion once that chain is in this tree. It assumes ly_bot ly < bp. *)
Definition dm_unwind_spec : Prop :=
forall (W : world tfibsegs) (ly : alayout) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
(this pc0 bp ra0 nfp0 : Z) (ch : list (Z * Z * Z)),
let H := w_H W in let m := mrestrict H mem in
let sp := bv_unsigned (getr regs 2) in let T := ly_T ly in
layout_ok ly -> img_cover ly ->
getr regs 10 = Z_to_bv 64 this -> getr regs 11 = Z_to_bv 64 pc0 -> getr regs 12 = Z_to_bv 64 bp ->
getr regs 13 = Z_to_bv 64 0 -> getr regs 14 = Z_to_bv 64 1 -> getr regs 15 = Z_to_bv 64 30 ->
getr regs 4 = Z_to_bv 64 TFIB_TP -> YK0s.ret_ok (getr regs 1) -> 0 <= pc0 < 2 ^ 64 ->
val_mem tfibsegs m 0xaccd8 1 1 -> val_mem tfibsegs m 0xab860 1 1 -> val_mem tfibsegs m 0xab864 4 0 ->
val_mem tfibsegs m (TFIB_TP - 88) 8 TFIB_TSD -> val_mem tfibsegs m TFIB_TSD 8 (ly_C ly) ->
val_mem tfibsegs m (ly_C ly + 152) 8 T -> val_mem tfibsegs m (T + 40) 1 0 ->
val_mem tfibsegs m (T + 8) 8 (ly_top ly) -> val_mem tfibsegs m (T + 16) 8 (ly_bot ly) ->
val_mem tfibsegs m (T + t_unwinding) 1 0 -> apresent H mem (T + t_unwinding) ->
val_mem tfibsegs m 0xa2a30 8 0x13baa0 -> val_mem tfibsegs m 0x13baa0 8 4096 ->
sp mod 16 = 0 -> ly_stk_lo ly <= sp - DM_UNW_STK -> (forall a, sp - DM_UNW_STK <= a < sp -> apresent H mem a) ->
this mod 8 = 0 -> ly_stk_lo ly <= this -> this + DM_BST <= sp - DM_UNW_STK \/ sp <= this ->
(forall a, this <= a < this + DM_BST -> apresent H mem a) ->
this + DM_BST <= bp - 16 -> sp <= bp - 16 -> ly_bot ly < bp -> bp <= ly_stk_hi ly -> bp mod 8 = 0 ->
rdword (aview tfibsegs H mem) (bp - 8) = Some ra0 -> rdword (aview tfibsegs H mem) (bp - 16) = Some nfp0 -> 4096 <= ra0 ->
(if bp + 16 <? ly_top ly
then (if bad_next bp (ly_top ly) nfp0 then ch = [] else bp + 16 <= nfp0 /\ fpchain (rdword (aview tfibsegs H mem)) nfp0 (ly_top ly) ch)
else ch = []) ->
SRr tfibsegs W (mkCfg (mkst regs (Z_to_bv 64 DM_UNW_PC) mem (seg_rom tfibsegs)) md)
(fun W' c' => W' = W /\ exists regs' mem' mat,
c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md) mat md) /\
regs_preserved regs regs' /\
(forall x : word, ~ (sp - DM_UNW_STK <= bv_unsigned x < sp) -> ~ (this + 8 <= bv_unsigned x < this + 12) ->
~ (this + 16 <= bv_unsigned x < this + 16 + 8 * 30) -> ~ (this + 2056 <= bv_unsigned x < this + DM_BST) ->
mem' x = mem x) /\
(forall a, apresent H mem a -> apresent H mem' a) /\
let tr := if bp + 16 <? ly_top ly then unwind_of_chain pc0 ((bp, ra0, nfp0) :: ch) else [pc0] in
val_mem tfibsegs (mrestrict H mem') (this + 8) 4 (Z.of_nat (length tr)) /\
(forall i, (i < length tr)%nat -> val_mem tfibsegs (mrestrict H mem') (this + 16 + 8 * Z.of_nat i) 8 (nth i tr 0)) /\
val_mem tfibsegs (mrestrict H mem') (this + 2056) 8 bp).

End b.

(* The walk of the bottom case. The seed is cgif's (AFl2.v SS_U0) without the frame at bp, which this case never
   reads, and with the condition stack bottom >=u bp in place of stack bottom <u bp. *)
Definition ub_lit8 (a v : Z) : YP09.region := YP09.mkRegion None a (a + 8) 0 0 [YP09.mkChunk a (CVal 8 (SLit v))].
Definition ub_lit4 (a v : Z) : YP09.region := YP09.mkRegion None a (a + 4) 0 0 [YP09.mkChunk a (CVal 4 (SLit v))].
Definition ub_lit1 (a v : Z) : YP09.region := YP09.mkRegion None a (a + 1) 0 0 [YP09.mkChunk a (CVal 1 (SLit v))].
Definition ub_atom8 (a : Z) (n : nat) : YP09.region := YP09.mkRegion None a (a + 8) 0 0 [YP09.mkChunk a (CVal 8 (SOff n 0))].
Definition ubT : nat := 32. Definition ubC : nat := 33. Definition ubTOP : nat := 34.
Definition UB_atoms : list (nat * afact) :=
[ (2%nat, mkAF (kHighMemBeg + DM_UNW_STK) kHighMemEnd 4);
(10%nat, mkAF kHighMemBeg kHighMemEnd 3);
(11%nat, mkAF 0 (2 ^ 64 - 1) 0);
(12%nat, mkAF kHighMemBeg kHighMemEnd 3);
(ubT, mkAF 4096 (CEIL_MAX - 4096) 12);
(ubC, mkAF 4096 (CEIL_MAX - 256) 3);
(ubTOP, mkAF (kHighMemBeg + kStackSpan) kHighMemEnd 12) ].
Definition UB_conds : list acond := [ mkAC BC_GEU (SOff ubTOP (- kStackSpan)) (SOff 12%nat 0) ].
Definition UB0F : facts := mkFacts UB_atoms UB_conds [].
Definition UBREGS0 : list sv :=
sr_set (sr_set (sr_set (sr_set sr_atoms 4%bv (SLit TFIB_TP)) 13%bv (SLit 0)) 14%bv (SLit 1)) 15%bv (SLit 30).
Definition UB_S : YP09.region := YP09.mkRegion (Some 2%nat) (- DM_UNW_STK) 0 (- DM_UNW_STK) 0 [].
Definition UB_O1a : YP09.region := YP09.mkRegion (Some 10%nat) 8 12 8 12 [].
Definition UB_O1b : YP09.region := YP09.mkRegion (Some 10%nat) 16 24 16 24 [].
Definition UB_O2 : YP09.region := YP09.mkRegion (Some 10%nat) 2056 2064 2056 2064 [].
Definition UB_C : YP09.region := YP09.mkRegion (Some ubC) 152 160 0 0 [YP09.mkChunk 152 (CVal 8 (SOff ubT 0))].
Definition UB_T1 : YP09.region := YP09.mkRegion (Some ubT) 8 41 0 0
[YP09.mkChunk 8 (CVal 8 (SOff ubTOP 0)); YP09.mkChunk 16 (CVal 8 (SOff ubTOP (- kStackSpan))); YP09.mkChunk 40 (CVal 1 (SLit 0))].
Definition UB_T2 : YP09.region := YP09.mkRegion (Some ubT) t_unwinding (t_unwinding + 1) t_unwinding (t_unwinding + 1)
[YP09.mkChunk t_unwinding (CVal 1 (SLit 0))].
Definition UBCONST : smem :=
[ ub_lit1 0xaccd8 1; ub_lit1 0xab860 1; ub_lit4 0xab864 0; ub_lit8 (TFIB_TP - 88) TFIB_TSD; ub_atom8 TFIB_TSD ubC;
ub_lit8 0xa2a30 0x13baa0; ub_lit8 0x13baa0 4096 ].
Definition UBMEM0 : smem := [UB_S; UB_O1a; UB_O1b; UB_O2] ++ UBCONST ++ [UB_C; UB_T1; UB_T2].
Definition UB_SS0 : sstate := mkSS DM_UNW_PC UBREGS0 UBMEM0 None UB0F.
Definition UB_F : sstate := Eval vm_compute in fst (sym_runN tfibsegs tfibtbl_rtA FUEL UB_SS0).
Lemma ub_run : sym_runN tfibsegs tfibtbl_rtA FUEL UB_SS0 = (UB_F, RS_stopped (SR_jalr (SOff 1 0))).
Proof. vm_compute. reflexivity. Qed.
Lemma ub_f_shape : ss_pc UB_F = DM_UNW_RET /\ ss_resv UB_F = None /\ windows (ss_mem UB_F) = windows UBMEM0.
Proof. vm_compute. repeat split; reflexivity. Qed.

Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Ltac numconst := ceil; unfold kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kStackSpan, t_unwinding, TFIB_IMG_END, DM_UNW_STK, DM_BST, TFIB_TP, TFIB_TSD, zcanon, M64 in *.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* AFl3.v *)
Lemma ub_region_ok_window : forall E (m : word -> option byte) n b lo hi wlo whi,
bv_unsigned (ew E n) = b -> 0 <= b + lo -> b + hi <= 2 ^ 64 ->
(forall a, b + wlo <= a < b + whi -> writable_at tfibsegs m a) ->
region_ok tfibsegs E m (YP09.mkRegion (Some n) lo hi wlo whi []).
Proof.
intros E m n b lo hi wlo whi Hn Hlo Hhi Hw. unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite Hn. split; [lia|]. split; [lia|]. split; [|constructor]. intros o Ho. apply Hw. lia.
Qed.
Lemma ub_region_ok_lit : forall E (m : word -> option byte) a (w : N) v,
val_mem tfibsegs m a (N.to_nat w) v -> 0 <= v < 2 ^ (8 * Z.of_N w) -> Z.of_N w <= 8 -> 0 <= a -> a + Z.of_N w <= 2 ^ 64 ->
region_ok tfibsegs E m (YP09.mkRegion None a (a + Z.of_N w) 0 0 [YP09.mkChunk a (CVal w (SLit v))]).
Proof.
intros E m a w v Hv Hr Hw Ha Hh. unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. apply Forall_cons; [|apply Forall_nil].
eapply chunk_ok_val; [reflexivity | exact Hr | exact Hw | rewrite Z.add_0_l; exact Hv].
Qed.
Lemma ub_region_ok_atom8 : forall E (m : word -> option byte) a k v,
val_mem tfibsegs m a 8 v -> ew E k = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= a -> a + 8 <= 2 ^ 64 ->
region_ok tfibsegs E m (ub_atom8 a k).
Proof.
intros E m a k v Hv Hk Hr Ha Hh. unfold region_ok, ub_atom8. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. apply Forall_cons; [|apply Forall_nil].
eapply (chunk_ok_val tfibsegs E m 0 a 8 (SOff k 0) v); [| exact Hr | cbn; lia | rewrite Z.add_0_l; exact Hv].
cbn [sv_denot]. rewrite Hk, unsigned_lit_small by exact Hr. f_equal. lia.
Qed.
Lemma ub_regs_preserved_intro : forall regs regs' : bvmap 5 word,
getr regs' 2%bv = getr regs 2%bv -> getr regs' 3%bv = getr regs 3%bv -> getr regs' 4%bv = getr regs 4%bv ->
getr regs' 8%bv = getr regs 8%bv -> getr regs' 9%bv = getr regs 9%bv -> getr regs' 18%bv = getr regs 18%bv ->
getr regs' 19%bv = getr regs 19%bv -> getr regs' 20%bv = getr regs 20%bv -> getr regs' 21%bv = getr regs 21%bv ->
getr regs' 22%bv = getr regs 22%bv -> getr regs' 23%bv = getr regs 23%bv -> getr regs' 24%bv = getr regs 24%bv ->
getr regs' 25%bv = getr regs 25%bv -> getr regs' 26%bv = getr regs 26%bv -> getr regs' 27%bv = getr regs 27%bv ->
regs_preserved regs regs'.
Proof.
intros regs regs'. intros. intros r Hr. unfold callee_saved in Hr.
assert (X : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
clear Hr.
destruct X as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]]]].
{ replace (Z_to_bv 5 2) with (2%bv : bv 5) by (apply bv_eq; reflexivity). assumption. }
{ replace (Z_to_bv 5 3) with (3%bv : bv 5) by (apply bv_eq; reflexivity). assumption. }
{ replace (Z_to_bv 5 4) with (4%bv : bv 5) by (apply bv_eq; reflexivity). assumption. }
{ replace (Z_to_bv 5 8) with (8%bv : bv 5) by (apply bv_eq; reflexivity). assumption. }
{ replace (Z_to_bv 5 9) with (9%bv : bv 5) by (apply bv_eq; reflexivity). assumption. }
{ replace (Z_to_bv 5 18) with (18%bv : bv 5) by (apply bv_eq; reflexivity). assumption. }
{ replace (Z_to_bv 5 19) with (19%bv : bv 5) by (apply bv_eq; reflexivity). assumption. }
{ replace (Z_to_bv 5 20) with (20%bv : bv 5) by (apply bv_eq; reflexivity). assumption. }
{ replace (Z_to_bv 5 21) with (21%bv : bv 5) by (apply bv_eq; reflexivity). assumption. }
{ replace (Z_to_bv 5 22) with (22%bv : bv 5) by (apply bv_eq; reflexivity). assumption. }
{ replace (Z_to_bv 5 23) with (23%bv : bv 5) by (apply bv_eq; reflexivity). assumption. }
{ replace (Z_to_bv 5 24) with (24%bv : bv 5) by (apply bv_eq; reflexivity). assumption. }
{ replace (Z_to_bv 5 25) with (25%bv : bv 5) by (apply bv_eq; reflexivity). assumption. }
{ replace (Z_to_bv 5 26) with (26%bv : bv 5) by (apply bv_eq; reflexivity). assumption. }
{ replace (Z_to_bv 5 27) with (27%bv : bv 5) by (apply bv_eq; reflexivity). assumption. }
Qed.

Section g.
Variables (W : world tfibsegs) (ly : alayout) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model).
Variables (this pc0 bp : Z).
#[local] Notation Hd := (w_H W).
#[local] Notation m0 := (mrestrict (w_H W) mem).
#[local] Notation sp := (bv_unsigned (getr regs 2%bv)).
#[local] Notation T := (ly_T ly).
#[local] Notation C := (ly_C ly).
#[local] Notation top := (ly_top ly).
Hypothesis LY : layout_ok ly.
Hypothesis IMG : img_cover ly.
Hypotheses (R10 : getr regs 10%bv = Z_to_bv 64 this) (R11 : getr regs 11%bv = Z_to_bv 64 pc0) (R12 : getr regs 12%bv = Z_to_bv 64 bp)
(R13 : getr regs 13%bv = Z_to_bv 64 0) (R14 : getr regs 14%bv = Z_to_bv 64 1) (R15 : getr regs 15%bv = Z_to_bv 64 30)
(R4 : getr regs 4%bv = Z_to_bv 64 TFIB_TP) (Hra : YK0s.ret_ok (getr regs 1%bv)) (Hpc0 : 0 <= pc0 < 2 ^ 64).
Hypotheses (V_inited : val_mem tfibsegs m0 0xaccd8 1 1) (V_tsdk1 : val_mem tfibsegs m0 0xab860 1 1) (V_tsdk2 : val_mem tfibsegs m0 0xab864 4 0)
(V_tp : val_mem tfibsegs m0 (TFIB_TP - 88) 8 TFIB_TSD) (V_tsd : val_mem tfibsegs m0 TFIB_TSD 8 C)
(V_ctx : val_mem tfibsegs m0 (C + 152) 8 T) (V_t40 : val_mem tfibsegs m0 (T + 40) 1 0)
(V_t8 : val_mem tfibsegs m0 (T + 8) 8 top) (V_t16 : val_mem tfibsegs m0 (T + 16) 8 (ly_bot ly))
(V_unw : val_mem tfibsegs m0 (T + t_unwinding) 1 0) (P_unw : apresent Hd mem (T + t_unwinding))
(V_psz1 : val_mem tfibsegs m0 0xa2a30 8 0x13baa0) (V_psz2 : val_mem tfibsegs m0 0x13baa0 8 4096).
Hypotheses (Hsp16 : sp mod 16 = 0) (Hsplo : ly_stk_lo ly <= sp - DM_UNW_STK) (P_stk : forall a, sp - DM_UNW_STK <= a < sp -> apresent Hd mem a)
(Hthis8 : this mod 8 = 0) (Hthislo : ly_stk_lo ly <= this) (Hthis_sp : this + DM_BST <= sp - DM_UNW_STK \/ sp <= this)
(P_this : forall a, this <= a < this + DM_BST -> apresent Hd mem a)
(Hthis_bp : this + DM_BST <= bp - 16) (Hsp_bp : sp <= bp - 16) (Hbot_bp : bp <= ly_bot ly) (Hbp_hi : bp <= ly_stk_hi ly) (Hbp8 : bp mod 8 = 0).

(* AFl4.v, with the bottom case's bp. *)
Lemma T_high : in_app T kThreadObjSize.
Proof. pose proof (lo_app ly LY) as HH. unfold owned_extents in HH. do 2 apply Forall_inv_tail in HH. apply Forall_inv in HH. exact HH. Qed.
Lemma C_high : in_app C 256.
Proof. pose proof (lo_app ly LY) as HH. unfold owned_extents in HH. do 6 apply Forall_inv_tail in HH. apply Forall_inv in HH. exact HH. Qed.
Lemma TC_disj : (T + kThreadObjSize <= C \/ C + 256 <= T) /\ (T + kThreadObjSize <= ly_stk_lo ly \/ ly_stk_lo ly + (ly_stk_hi ly - ly_stk_lo ly) <= T) /\
(C + 256 <= ly_stk_lo ly \/ ly_stk_lo ly + (ly_stk_hi ly - ly_stk_lo ly) <= C).
Proof.
pose proof (lo_disj ly LY) as HD. unfold static_extents, owned_extents in HD. cbn [pairwise app] in HD.
destruct HD as (_ & _ & D3 & _ & _ & _ & D7 & _).
pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail D3)))) as X1.
pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail D3)))))) as X2.
pose proof (Forall_inv (Forall_inv_tail D7)) as X3. unfold zdisjoint in X1, X2, X3. cbn [fst snd] in X1, X2, X3.
split; [exact X1 | split; [exact X2 | exact X3]].
Qed.
Lemma top_facts : ly_stk_lo ly <= ly_bot ly /\ ly_bot ly < top <= ly_stk_hi ly /\ top mod 4096 = 0 /\ ly_stk_hi ly <= kHighMemEnd /\ kHighMemBeg <= ly_stk_lo ly.
Proof. pose proof (lo_top ly LY) as (A1 & A2 & A3 & A4 & A5 & A6 & A7). unfold page_aligned in A3. repeat split; try assumption; apply A2. Qed.
Lemma bot_eq : ly_bot ly = top - kStackSpan. Proof. reflexivity. Qed.
Lemma T_zone : zone3 T kThreadObjSize.
Proof.
pose proof (lo_disj ly LY) as HD. unfold static_extents, owned_extents in HD. cbn [pairwise app] in HD.
destruct HD as (_ & _ & D3 & _).
pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail D3))))))) as X.
exact (zone3_intro ly T kThreadObjSize IMG ltac:(unfold kThreadObjSize; lia) T_high X).
Qed.
Lemma C_zone : zone3 C 256.
Proof.
pose proof (lo_disj ly LY) as HD. unfold static_extents, owned_extents in HD. cbn [pairwise app] in HD.
destruct HD as (_ & _ & _ & _ & _ & _ & D7 & _).
pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail D7))) as X.
exact (zone3_intro ly C 256 IMG ltac:(lia) C_high X).
Qed.
Ltac zoneTC := pose proof T_zone as TZ; pose proof C_zone as CZ;
unfold zone3, zone3cases, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kHighMemBeg, kThreadObjSize in TZ, CZ.
Lemma T_off : forall a, T <= a < T + kThreadObjSize -> off_img a.
Proof. intros a Ha. exact (zone3_off_img T kThreadObjSize a T_zone Ha). Qed.
Lemma unw_off : off_img (T + t_unwinding).
Proof. apply T_off. unfold t_unwinding, kThreadObjSize. lia. Qed.
Lemma zone_facts :
0x10007fff8000 <= ly_stk_lo ly /\ ly_stk_lo ly <= top - 8388608 /\ top <= ly_stk_hi ly /\ ly_stk_hi ly <= 0x800000000000 /\
4096 <= T /\ T + 4096 <= 140737479966720 /\ 4096 <= C /\ C + 256 <= 140737479966720 /\
(T + 4096 <= C \/ C + 256 <= T) /\ (T + 4096 <= ly_stk_lo ly \/ ly_stk_hi ly <= T) /\ (C + 256 <= ly_stk_lo ly \/ ly_stk_hi ly <= C) /\
ly_stk_lo ly <= sp - 144 /\ sp <= bp - 16 /\ ly_stk_lo ly <= this /\ this + 2064 <= bp - 16 /\ (this + 2064 <= sp - 144 \/ sp <= this) /\
bp <= top - 8388608 /\ bp <= ly_stk_hi ly.
Proof.
pose proof T_high as [B1 B2]. pose proof C_high as [B3 B4]. pose proof TC_disj as (B5 & B6 & B7). pose proof top_facts as (B8 & B9 & B10 & B11 & B12).
pose proof Hsplo as C1. pose proof Hsp_bp as C2. pose proof Hthislo as C3. pose proof Hthis_bp as C4. pose proof Hthis_sp as C5.
pose proof Hbot_bp as C6. pose proof Hbp_hi as C7.
clear - B1 B2 B3 B4 B5 B6 B7 B8 B9 B10 B11 B12 C1 C2 C3 C4 C5 C6 C7.
ceil; unfold in_app, ly_bot, kHighMemBeg, kHighMemEnd, kLowShadowBeg, ASAN_CEIL, kThreadObjSize, kStackSpan, DM_UNW_STK, DM_BST in *.
repeat split; lia.
Qed.
Ltac zone := pose proof zone_facts as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8 & Z9 & Z10 & Z11 & Z12 & Z13 & Z14 & Z15 & Z16 & Z17 & Z18).
Definition XW : list word := [Z_to_bv 64 T; Z_to_bv 64 C; Z_to_bv 64 top].
Definition E0 : env := Ereg regs XW.
Lemma EaT : ew E0 ubT = Z_to_bv 64 T. Proof. reflexivity. Qed.
Lemma EaC : ew E0 ubC = Z_to_bv 64 C. Proof. reflexivity. Qed.
Lemma EaTOP : ew E0 ubTOP = Z_to_bv 64 top. Proof. reflexivity. Qed.
Lemma EaT' : ew E0 32 = Z_to_bv 64 T. Proof. reflexivity. Qed.
Lemma EaTOP' : ew E0 34 = Z_to_bv 64 top. Proof. reflexivity. Qed.
Lemma Er (k : nat) (r : bv 5) : Z.of_nat k = bv_unsigned r -> ew E0 k = getr regs r.
Proof. intros Hk. exact (ew_Ereg_nat regs XW k r Hk). Qed.
Lemma E1 : ew E0 1 = getr regs 1%bv. Proof. exact (Er 1 1%bv eq_refl). Qed.
Lemma E2 : ew E0 2 = getr regs 2%bv. Proof. exact (Er 2 2%bv eq_refl). Qed.
Lemma E10 : ew E0 10 = Z_to_bv 64 this. Proof. rewrite <- R10. exact (Er 10 10%bv eq_refl). Qed.
Lemma E11 : ew E0 11 = Z_to_bv 64 pc0. Proof. rewrite <- R11. exact (Er 11 11%bv eq_refl). Qed.
Lemma E12 : ew E0 12 = Z_to_bv 64 bp. Proof. rewrite <- R12. exact (Er 12 12%bv eq_refl). Qed.
Lemma sp_range : 0 <= sp < 2 ^ 64. Proof. apply u64_range. Qed.
#[local] Notation msU0 := (mkst regs (Z_to_bv 64 DM_UNW_PC) mem (seg_rom tfibsegs)).
Lemma REG0_ok : Forall (region_ok tfibsegs E0 m0) UBMEM0.
Proof.
zone. pose proof Hpc0 as PR. pose proof sp_range as SR.
unfold UBMEM0, UBCONST, UB_S, UB_O1a, UB_O1b, UB_O2, UB_C, UB_T1, UB_T2, ub_lit1, ub_lit4, ub_lit8. cbn [app].
apply Forall_cons. { apply (region_ok_stack tfibsegs E0 m0 2 sp (- DM_UNW_STK)); [rewrite E2; reflexivity | clear - Z1 Z12; numconst; lia | clear - SR; lia |].
intros a Ha. apply apresent_writable; [clear - Ha Z1 Z12 SR; numconst; lia | apply P_stk; exact Ha]. }
apply Forall_cons. { apply (ub_region_ok_window E0 m0 10 this); [rewrite E10; apply unsigned_lit_small; clear - Z1 Z14 Z15 Z18 Z4; numconst; lia
| clear - Z1 Z14; numconst; lia | clear - Z15 Z18 Z4; numconst; lia |].
intros a Ha. apply apresent_writable; [clear - Ha Z1 Z14 Z15 Z18 Z4; numconst; lia | apply P_this; clear - Ha; numconst; lia]. }
apply Forall_cons. { apply (ub_region_ok_window E0 m0 10 this); [rewrite E10; apply unsigned_lit_small; clear - Z1 Z14 Z15 Z18 Z4; numconst; lia
| clear - Z1 Z14; numconst; lia | clear - Z15 Z18 Z4; numconst; lia |].
intros a Ha. apply apresent_writable; [clear - Ha Z1 Z14 Z15 Z18 Z4; numconst; lia | apply P_this; clear - Ha; numconst; lia]. }
apply Forall_cons. { apply (ub_region_ok_window E0 m0 10 this); [rewrite E10; apply unsigned_lit_small; clear - Z1 Z14 Z15 Z18 Z4; numconst; lia
| clear - Z1 Z14; numconst; lia | clear - Z15 Z18 Z4; numconst; lia |].
intros a Ha. apply apresent_writable; [clear - Ha Z1 Z14 Z15 Z18 Z4; numconst; lia | apply P_this; clear - Ha; numconst; lia]. }
apply Forall_cons. { apply (ub_region_ok_lit E0 m0 0xaccd8 1 1 V_inited); clear; numconst; cbn; lia. }
apply Forall_cons. { apply (ub_region_ok_lit E0 m0 0xab860 1 1 V_tsdk1); clear; numconst; cbn; lia. }
apply Forall_cons. { apply (ub_region_ok_lit E0 m0 0xab864 4 0 V_tsdk2); clear; numconst; cbn; lia. }
apply Forall_cons. { apply (ub_region_ok_lit E0 m0 (TFIB_TP - 88) 8 TFIB_TSD V_tp); clear; numconst; cbn; lia. }
apply Forall_cons. { apply (ub_region_ok_atom8 E0 m0 TFIB_TSD ubC C V_tsd EaC); clear - Z7 Z8; numconst; lia. }
apply Forall_cons. { apply (ub_region_ok_lit E0 m0 0xa2a30 8 0x13baa0 V_psz1); clear; numconst; cbn; lia. }
apply Forall_cons. { apply (ub_region_ok_lit E0 m0 0x13baa0 8 4096 V_psz2); clear; numconst; cbn; lia. }
apply Forall_cons. {   unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite EaC, unsigned_lit_small by (clear - Z7 Z8; numconst; lia).
split; [clear - Z7; numconst; lia|]. split; [clear - Z8; numconst; lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [| apply Forall_nil].
eapply (chunk_ok_val tfibsegs E0 m0 C 152 8 (SOff ubT 0) T); [cbn [sv_denot]; rewrite EaT, unsigned_lit_small by (clear - Z5 Z6; numconst; lia); f_equal; lia
| clear - Z5 Z6; numconst; lia | clear; numconst; cbn; lia | exact V_ctx]. }
apply Forall_cons. {   unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite EaT, unsigned_lit_small by (clear - Z5 Z6; numconst; lia).
split; [clear - Z5; numconst; lia|]. split; [clear - Z6; numconst; lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]].
- eapply (chunk_ok_val tfibsegs E0 m0 T 8 8 (SOff ubTOP 0) top); [cbn [sv_denot]; rewrite EaTOP, unsigned_lit_small by (clear - Z1 Z2 Z3 Z4; numconst; lia); f_equal; lia
| clear - Z1 Z2 Z3 Z4; numconst; lia | clear; numconst; cbn; lia | exact V_t8].
- eapply (chunk_ok_val tfibsegs E0 m0 T 16 8 (SOff ubTOP (- kStackSpan)) (top - kStackSpan));
[cbn [sv_denot]; rewrite EaTOP, unsigned_lit_small by (clear - Z1 Z2 Z3 Z4; numconst; lia); f_equal; lia
| clear - Z1 Z2 Z3 Z4; numconst; lia | clear; numconst; cbn; lia | rewrite <- bot_eq; exact V_t16].
- eapply (chunk_ok_val tfibsegs E0 m0 T 40 1 (SLit 0) 0); [reflexivity | clear; numconst; cbn; lia | cbn; lia | exact V_t40]. }
apply Forall_cons; [| apply Forall_nil].
{   unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite EaT, unsigned_lit_small by (clear - Z5 Z6; numconst; lia).
split; [clear - Z5; numconst; lia|]. split; [clear - Z6; numconst; lia|]. split.
{ intros o Ho. replace (T + o) with (T + t_unwinding) by (clear - Ho; lia). apply apresent_writable_off; [exact unw_off | exact P_unw]. }
apply Forall_cons; [| apply Forall_nil].
eapply (chunk_ok_val tfibsegs E0 m0 T t_unwinding 1 (SLit 0) 0); [reflexivity | clear; numconst; cbn; lia | cbn; lia | exact V_unw]. }
Qed.
Lemma PAIRS_ok : pairwise_disjoint E0 UBMEM0.
Proof.
zone. pose proof sp_range as SR.
apply pairwise_disjoint_of_extents. unfold UBMEM0, UBCONST, UB_S, UB_O1a, UB_O1b, UB_O2, UB_C, UB_T1, UB_T2, ub_lit1, ub_lit4, ub_lit8, ub_atom8, extent_of_region.
cbn [map app YP09.r_base YP09.r_lo YP09.r_hi base_val].
rewrite E2, E10, EaT, EaC. rewrite !unsigned_lit_small by (clear - Z1 Z2 Z4 Z5 Z6 Z7 Z8 Z14 Z15 Z17 Z18; numconst; lia).
zoneTC.
clear - Z1 Z2 Z3 Z4 Z5 Z6 Z7 Z8 Z9 Z10 Z11 Z12 Z13 Z14 Z15 Z16 Z17 Z18 SR TZ CZ.
numconst. cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
repeat split; lia.
Qed.
Lemma FACTS_ok : facts_ok E0 UB0F.
Proof.
zone. pose proof Hpc0 as PR. pose proof sp_range as SR.
pose proof top_facts as (_ & _ & TA & _). pose proof (lo_T_al ly LY) as TAL. pose proof (lo_C_al ly LY) as CAL. unfold page_aligned in TAL.
pose proof Hsp16 as A16. pose proof Hthis8 as A8. pose proof Hbp8 as B8.
assert (AF : forall k X lo hi al, ew E0 k = Z_to_bv 64 X -> 0 <= X < 2 ^ 64 -> lo <= X <= hi -> X mod 2 ^ al = 0 -> 0 <= al <= 64 -> afact_ok E0 k (mkAF lo hi al)).
{ clear. intros k X lo hi al HE HX HB HM HA. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HE. rewrite unsigned_lit_small by exact HX. repeat split; lia. }
assert (E2' : ew E0 2 = Z_to_bv 64 sp) by (rewrite E2; symmetry; apply Z_to_bv_bv_unsigned).
split; [| split; [| exact I]].
- unfold UB0F, UB_atoms. cbn [f_atoms atoms_ok]. unfold ubT, ubC, ubTOP.
split. { apply (AF 2%nat sp _ _ _ E2'); clear - SR Z1 Z12 Z13 Z18 Z4 A16; [lia | numconst; lia | exact A16 | lia]. }
split. { apply (AF 10%nat this _ _ _ E10); clear - Z1 Z14 Z15 Z18 Z4 A8; [numconst; lia | numconst; lia | exact A8 | lia]. }
split. { apply (AF 11%nat pc0 _ _ _ E11); clear - PR; [lia | lia | apply Z.mod_1_r | lia]. }
split. { apply (AF 12%nat bp _ _ _ E12); clear - Z1 Z14 Z15 Z18 Z4 B8; [numconst; lia | numconst; lia | exact B8 | lia]. }
split. { apply (AF 32%nat T _ _ _ EaT); clear - Z5 Z6 TAL; [numconst; lia | numconst; lia | exact TAL | lia]. }
split. { apply (AF 33%nat C _ _ _ EaC); clear - Z7 Z8 CAL; [numconst; lia | numconst; lia | exact CAL | lia]. }
split; [| exact I]. { apply (AF 34%nat top _ _ _ EaTOP); clear - Z1 Z2 Z3 Z4 TA; [numconst; lia | numconst; lia | exact TA | lia]. }
- unfold UB0F, UB_conds. cbn [f_conds conds_ok]. split; [| exact I].
unfold acond_ok. cbn [ac_c ac_a ac_b]. unfold branch_taken, bv_ltu. rewrite !denot_SOff, EaTOP, E12.
rewrite !unsigned_lit_small by (clear - Z1 Z2 Z3 Z4 Z14 Z15 Z18; numconst; lia). unfold zcanon.
rewrite !Z.mod_small by (clear - Z1 Z2 Z3 Z4 Z14 Z15 Z18; numconst; lia).
apply Bool.negb_true_iff. apply Z.ltb_ge. clear - Z17. numconst. lia.
Qed.
Lemma SEED_ok : st_ok tfibsegs E0 UB_SS0 (restrict Hd msU0).
Proof.
rewrite restrict_mkst_fx. unfold UB_SS0, UBREGS0. apply (entry_st_ok_full tfibsegs).
- apply regs_ok_pin; [| intros X; discriminate | cbn [sv_denot]; exact R15].
apply regs_ok_pin; [| intros X; discriminate | cbn [sv_denot]; exact R14].
apply regs_ok_pin; [| intros X; discriminate | cbn [sv_denot]; exact R13].
apply regs_ok_pin; [apply regs_ok_Ereg | intros X; discriminate | cbn [sv_denot]; exact R4].
- vm_compute. reflexivity.
- cbn [ms_mem mkst]. exact REG0_ok.
- exact PAIRS_ok.
- exact FACTS_ok.
Qed.
(* AFl4.v unw_byte_same *)
Lemma unw_byte_same : forall (m' : word -> option byte),
val_mem tfibsegs (mrestrict Hd m') (T + t_unwinding) 1 0 -> m' (Z_to_bv 64 (T + t_unwinding)) = mem (Z_to_bv 64 (T + t_unwinding)).
Proof.
intros m' Hv. pose proof P_unw as [Hh _].
pose proof (V_unw 0%nat ltac:(lia)) as A. pose proof (Hv 0%nat ltac:(lia)) as B. rewrite Z.add_0_r in A, B.
unfold mbyte in A, B. unfold mrestrict in A, B. rewrite Hh in A, B.
rewrite (seg_rom_none_off (T + t_unwinding) unw_off) in A, B.
destruct (m' (Z_to_bv 64 (T + t_unwinding))) as [b'|]; [|discriminate B].
destruct (mem (Z_to_bv 64 (T + t_unwinding))) as [b|]; [|discriminate A]. congruence.
Qed.
(* the five write windows of the walk, all off the image *)
Definition UBWIN (a : Z) : Prop :=
(sp - DM_UNW_STK <= a < sp) \/ (this + 8 <= a < this + 12) \/ (this + 16 <= a < this + 24) \/ (this + 2056 <= a < this + DM_BST) \/
(T + t_unwinding <= a < T + t_unwinding + 1).
Lemma ub_wrange : forall a, in_wrange E0 UBMEM0 a -> UBWIN a.
Proof.
intros a (r & Hin & Hr). zone. pose proof sp_range as SR. unfold UBWIN.
assert (TH : bv_unsigned (ew E0 10) = this) by (rewrite E10; apply unsigned_lit_small; clear - Z1 Z14 Z15 Z18 Z4; numconst; lia).
assert (TT : bv_unsigned (ew E0 ubT) = T) by (rewrite EaT; apply unsigned_lit_small; clear - Z5 Z6; numconst; lia).
assert (TS : bv_unsigned (ew E0 2) = sp) by (rewrite E2; reflexivity).
unfold UBMEM0, UBCONST, UB_S, UB_O1a, UB_O1b, UB_O2, UB_C, UB_T1, UB_T2, ub_lit1, ub_lit4, ub_lit8, ub_atom8 in Hin. cbn [app] in Hin.
destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]];
cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; unfold DM_BST, DM_UNW_STK in *.
- left. rewrite TS in Hr. lia.
- right. left. rewrite TH in Hr. lia.
- right. right. left. rewrite TH in Hr. lia.
- right. right. right. left. rewrite TH in Hr. lia.
- lia.
- lia.
- lia.
- lia.
- lia.
- lia.
- lia.
- lia.
- lia.
- right. right. right. right. rewrite TT in Hr. lia.
Qed.
Lemma UBWIN_off : forall a, UBWIN a -> off_img a.
Proof.
intros a Ha. destruct (Z.eq_dec a (T + t_unwinding)) as [->|Hne]; [exact unw_off|]. right.
zone. pose proof sp_range as SR. unfold UBWIN in Ha. clear - Ha Hne Z1 Z12 Z13 Z14 Z15 Z4 Z18 SR. numconst. lia.
Qed.
(* AFl3.v in_wrangeb, AFl4.v pres_after_run_off *)
Definition in_wrangeb (E : env) (rs : smem) (a : Z) : bool :=
existsb (fun r => (base_val E (YP09.r_base r) + YP09.r_wlo r <=? a) && (a <? base_val E (YP09.r_base r) + YP09.r_whi r))%bool rs.
Lemma in_wrangeb_false : forall E rs a, in_wrangeb E rs a = false -> ~ in_wrange E rs a.
Proof.
intros E rs a H (r & Hin & Ha). unfold in_wrangeb in H.
assert (X : existsb (fun r => (base_val E (YP09.r_base r) + YP09.r_wlo r <=? a) && (a <? base_val E (YP09.r_base r) + YP09.r_whi r))%bool rs = true).
{ apply existsb_exists. exists r. split; [exact Hin|]. apply andb_true_iff. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
rewrite X in H. discriminate H.
Qed.
Lemma in_wrangeb_true : forall E rs a, in_wrangeb E rs a = true ->
exists i r, nth_error rs i = Some r /\ base_val E (YP09.r_base r) + YP09.r_wlo r <= a < base_val E (YP09.r_base r) + YP09.r_whi r.
Proof.
intros E rs a H. unfold in_wrangeb in H. apply existsb_exists in H as (r & Hin & Hb).
apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
destruct (In_nth_error _ _ Hin) as [i Hi]. exists i, r. split; [exact Hi | lia].
Qed.
Lemma in_wrange_of_windows : forall E rs rs' a, windows rs' = windows rs -> in_wrange E rs a -> in_wrange E rs' a.
Proof.
intros E rs rs' a Hw (r & Hin & Hr).
assert (X : In (YP09.r_base r, YP09.r_wlo r, YP09.r_whi r) (windows rs')).
{ rewrite Hw. unfold windows. exact (in_map (fun r0 => (YP09.r_base r0, YP09.r_wlo r0, YP09.r_whi r0)) rs r Hin). }
unfold windows in X. apply in_map_iff in X as (r' & Heq & Hin'). injection Heq as H1 H2 H3.
exists r'. split; [exact Hin'|]. rewrite H1, H2, H3. exact Hr.
Qed.
Lemma pres_after_run_off : forall E ss' rs (ms ms' : machine_state),
st_ok tfibsegs E ss' (restrict Hd ms') -> frame_of E rs (ms_mem ms) (ms_mem ms') -> windows (ss_mem ss') = windows rs ->
(forall a, in_wrange E rs a -> off_img a) ->
forall a, apresent Hd (ms_mem ms) a -> apresent Hd (ms_mem ms') a.
Proof.
intros E ss' rs ms ms' HS HF Hws Hhi a Ha.
set (x := Z_to_bv 64 a). assert (Ex : Z_to_bv 64 (bv_unsigned x) = x) by apply Z_to_bv_bv_unsigned.
destruct (in_wrangeb E (ss_mem ss') (bv_unsigned x)) eqn:Hb.
- destruct (in_wrangeb_true E _ _ Hb) as (i & r & Hi & Hr).
assert (P : apresent Hd (ms_mem ms') (bv_unsigned x)).
{ apply (st_ok_window_apresent_off Hd E ss' ms' i r _ HS Hi Hr). apply Hhi.
apply (in_wrange_of_windows E (ss_mem ss') rs); [symmetry; exact Hws|]. exists r. split; [exact (nth_error_In _ _ Hi) | exact Hr]. }
unfold apresent in P |- *. rewrite Ex in P. exact P.
- apply (apresent_same Hd (ms_mem ms)); [| exact Ha]. apply (HF x). intros Hw.
exact (in_wrangeb_false E _ _ Hb (in_wrange_of_windows E rs (ss_mem ss') _ Hws Hw)).
Qed.
(* AFl3.v chunk_val_at and memv *)
Lemma chunk_val_at : forall (H : word -> bool) E ss ms i j r off (n : BinNums.N) e v a,
st_ok tfibsegs E ss (restrict H ms) -> nth_error (ss_mem ss) i = Some r ->
nth_error (YP09.r_chunks r) j = Some (YP09.mkChunk off (CVal n e)) ->
a = base_val E (YP09.r_base r) + off ->
sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ (8 * Z.of_N n) -> Z.of_N n <= 8 ->
val_mem tfibsegs (mrestrict H (ms_mem ms)) a (N.to_nat n) v.
Proof. intros H E ss ms i j r off n e v a HS Hi Hj -> He Hv Hn. eapply st_ok_chunk_val; eassumption. Qed.
Ltac memv HS i j :=
lazymatch goal with |- val_mem _ _ ?a ?n ?v =>
let nn := lazymatch n with 1%nat => constr:(1%N) | 2%nat => constr:(2%N) | 4%nat => constr:(4%N) | _ => constr:(8%N) end in
lazymatch type of HS with st_ok _ ?E ?ss (restrict ?H ?ms) =>
eapply (chunk_val_at H E ss ms i j _ _ nn _ v a HS);
[ reflexivity | reflexivity | cbn [base_val YP09.r_base]
| | lazymatch goal with |- _ <= _ < ?p => let q := eval vm_compute in p in change p with q end
| cbn; lia ]
end
end.
Lemma ub_main : SRr tfibsegs W (mkCfg msU0 md) (dm_unw_post W regs mem md this bp [pc0]).
Proof.
pose proof AF0x.Hwx_tfa as Hwx. pose proof SEED_ok as HS. zone.
apply (SRr_run_gen tfibsegs tfibtbl_rtA tfibtbl_rtA_ok Hwx W FUEL E0 UB_SS0 UB_F (RS_stopped (SR_jalr (SOff 1 0))) msU0 md _ HS ub_run).
intros ms mat HSf HF _. cbv iota in HSf. cbn [ms_mem mkst] in HF.
pose proof ub_f_shape as (Hpc & Hrv & Hws).
apply (SRr_ret_at tfibsegs tfibtbl_rtA tfibtbl_rtA_ok Hwx W E0 UB_F ms _ _ HSf Hrv); [rewrite Hpc; vm_compute; reflexivity|].
intros mat'. rewrite wvb_collapse. split; [reflexivity|].
exists (ms_regs ms), (ms_mem ms), mat'.
rreg HSf (1%bv : bv 5) Q1. rewrite E1 in Q1.
split. { rewrite Q1. unfold YK0s.ret_ok in Hra. rewrite Hra. reflexivity. }
split. { apply ub_regs_preserved_intro.
- rreg HSf (2%bv : bv 5) Q. rewrite Q. exact E2.
- rreg HSf (3%bv : bv 5) Q. rewrite Q. exact (Er 3 3%bv eq_refl).
- rreg HSf (4%bv : bv 5) Q. rewrite Q. symmetry. exact R4.
- rreg HSf (8%bv : bv 5) Q. rewrite Q. exact (Er 8 8%bv eq_refl).
- rreg HSf (9%bv : bv 5) Q. rewrite Q. exact (Er 9 9%bv eq_refl).
- rreg HSf (18%bv : bv 5) Q. rewrite Q. exact (Er 18 18%bv eq_refl).
- rreg HSf (19%bv : bv 5) Q. rewrite Q. exact (Er 19 19%bv eq_refl).
- rreg HSf (20%bv : bv 5) Q. rewrite Q. exact (Er 20 20%bv eq_refl).
- rreg HSf (21%bv : bv 5) Q. rewrite Q. exact (Er 21 21%bv eq_refl).
- rreg HSf (22%bv : bv 5) Q. rewrite Q. exact (Er 22 22%bv eq_refl).
- rreg HSf (23%bv : bv 5) Q. rewrite Q. exact (Er 23 23%bv eq_refl).
- rreg HSf (24%bv : bv 5) Q. rewrite Q. exact (Er 24 24%bv eq_refl).
- rreg HSf (25%bv : bv 5) Q. rewrite Q. exact (Er 25 25%bv eq_refl).
- rreg HSf (26%bv : bv 5) Q. rewrite Q. exact (Er 26 26%bv eq_refl).
- rreg HSf (27%bv : bv 5) Q. rewrite Q. exact (Er 27 27%bv eq_refl). }
assert (THIS : bv_unsigned (ew E0 10) = this).
{ rewrite E10. apply unsigned_lit_small. clear - Z1 Z14 Z15 Z18 Z4; numconst; lia. }
assert (UNW : val_mem tfibsegs (mrestrict Hd (ms_mem ms)) (T + t_unwinding) 1 0).
{ memv HSf 13%nat 0%nat; [rewrite EaT', unsigned_lit_small by (clear - Z5 Z6; numconst; lia); reflexivity | reflexivity | clear; lia]. }
split.
{   intros x N1 N2 N3 N4.
destruct (Z.eq_dec (bv_unsigned x) (T + t_unwinding)) as [Ex | Nx].
- rewrite <- (Z_to_bv_bv_unsigned 64 x), Ex. apply unw_byte_same. exact UNW.
- apply HF. intros Hw. pose proof (ub_wrange _ Hw) as X. unfold UBWIN in X. clear - X N1 N2 N3 N4 Nx. numconst. lia. }
split.
{   intros a Ha. apply (pres_after_run_off E0 UB_F UBMEM0 msU0 ms HSf HF Hws); [|exact Ha].
intros a' Ha'. exact (UBWIN_off a' (ub_wrange a' Ha')). }
split.
{   memv HSf 1%nat 0%nat; [rewrite THIS; reflexivity | reflexivity | cbn; lia]. }
split.
{   intros i Hi. cbn [length] in Hi. destruct i as [|i]; [|lia].
memv HSf 2%nat 0%nat; [rewrite THIS; lia | cbn [sv_denot]; rewrite E11, unsigned_lit_small, Z.add_0_r by exact Hpc0; reflexivity | exact Hpc0]. }
memv HSf 3%nat 0%nat; [rewrite THIS; reflexivity | cbn [sv_denot]; rewrite E12, unsigned_lit_small, Z.add_0_r by (clear - Z1 Z14 Z15 Z18 Z4; numconst; lia); reflexivity
| clear - Z1 Z14 Z15 Z18 Z4; numconst; lia].
Qed.
End g.

(* The bottom case of the unwinder call: cgif's premises with bp <= ly_bot in place of ly_bot < bp, and
   without the frame at bp, which this case never reads. *)
Theorem dm_unwind_bot : forall (W : world tfibsegs) (ly : alayout) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
(this pc0 bp : Z),
let H := w_H W in let m := mrestrict H mem in
let sp := bv_unsigned (getr regs 2) in let T := ly_T ly in
layout_ok ly -> img_cover ly ->
getr regs 10 = Z_to_bv 64 this -> getr regs 11 = Z_to_bv 64 pc0 -> getr regs 12 = Z_to_bv 64 bp ->
getr regs 13 = Z_to_bv 64 0 -> getr regs 14 = Z_to_bv 64 1 -> getr regs 15 = Z_to_bv 64 30 ->
getr regs 4 = Z_to_bv 64 TFIB_TP -> YK0s.ret_ok (getr regs 1) -> 0 <= pc0 < 2 ^ 64 ->
val_mem tfibsegs m 0xaccd8 1 1 -> val_mem tfibsegs m 0xab860 1 1 -> val_mem tfibsegs m 0xab864 4 0 ->
val_mem tfibsegs m (TFIB_TP - 88) 8 TFIB_TSD -> val_mem tfibsegs m TFIB_TSD 8 (ly_C ly) ->
val_mem tfibsegs m (ly_C ly + 152) 8 T -> val_mem tfibsegs m (T + 40) 1 0 ->
val_mem tfibsegs m (T + 8) 8 (ly_top ly) -> val_mem tfibsegs m (T + 16) 8 (ly_bot ly) ->
val_mem tfibsegs m (T + t_unwinding) 1 0 -> apresent H mem (T + t_unwinding) ->
val_mem tfibsegs m 0xa2a30 8 0x13baa0 -> val_mem tfibsegs m 0x13baa0 8 4096 ->
sp mod 16 = 0 -> ly_stk_lo ly <= sp - DM_UNW_STK -> (forall a, sp - DM_UNW_STK <= a < sp -> apresent H mem a) ->
this mod 8 = 0 -> ly_stk_lo ly <= this -> this + DM_BST <= sp - DM_UNW_STK \/ sp <= this ->
(forall a, this <= a < this + DM_BST -> apresent H mem a) ->
this + DM_BST <= bp - 16 -> sp <= bp - 16 -> bp <= ly_bot ly -> bp <= ly_stk_hi ly -> bp mod 8 = 0 ->
SRr tfibsegs W (mkCfg (mkst regs (Z_to_bv 64 DM_UNW_PC) mem (seg_rom tfibsegs)) md)
(dm_unw_post W regs mem md this bp [pc0]).
Proof.
intros W ly regs mem md this pc0 bp H m sp T. intros.
apply (ub_main W ly regs mem md this pc0 bp); assumption.
Qed.

(* Both cases in one: the trace is [pc0] when bp is at or below the stack bottom, else cgif's. *)
Theorem dm_unwind_any : dm_unwind_spec ->
forall (W : world tfibsegs) (ly : alayout) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
(this pc0 bp ra0 nfp0 : Z) (ch : list (Z * Z * Z)),
let H := w_H W in let m := mrestrict H mem in
let sp := bv_unsigned (getr regs 2) in let T := ly_T ly in
layout_ok ly -> img_cover ly ->
getr regs 10 = Z_to_bv 64 this -> getr regs 11 = Z_to_bv 64 pc0 -> getr regs 12 = Z_to_bv 64 bp ->
getr regs 13 = Z_to_bv 64 0 -> getr regs 14 = Z_to_bv 64 1 -> getr regs 15 = Z_to_bv 64 30 ->
getr regs 4 = Z_to_bv 64 TFIB_TP -> YK0s.ret_ok (getr regs 1) -> 0 <= pc0 < 2 ^ 64 ->
val_mem tfibsegs m 0xaccd8 1 1 -> val_mem tfibsegs m 0xab860 1 1 -> val_mem tfibsegs m 0xab864 4 0 ->
val_mem tfibsegs m (TFIB_TP - 88) 8 TFIB_TSD -> val_mem tfibsegs m TFIB_TSD 8 (ly_C ly) ->
val_mem tfibsegs m (ly_C ly + 152) 8 T -> val_mem tfibsegs m (T + 40) 1 0 ->
val_mem tfibsegs m (T + 8) 8 (ly_top ly) -> val_mem tfibsegs m (T + 16) 8 (ly_bot ly) ->
val_mem tfibsegs m (T + t_unwinding) 1 0 -> apresent H mem (T + t_unwinding) ->
val_mem tfibsegs m 0xa2a30 8 0x13baa0 -> val_mem tfibsegs m 0x13baa0 8 4096 ->
sp mod 16 = 0 -> ly_stk_lo ly <= sp - DM_UNW_STK -> (forall a, sp - DM_UNW_STK <= a < sp -> apresent H mem a) ->
this mod 8 = 0 -> ly_stk_lo ly <= this -> this + DM_BST <= sp - DM_UNW_STK \/ sp <= this ->
(forall a, this <= a < this + DM_BST -> apresent H mem a) ->
this + DM_BST <= bp - 16 -> sp <= bp - 16 -> bp <= ly_stk_hi ly -> bp mod 8 = 0 ->
rdword (aview tfibsegs H mem) (bp - 8) = Some ra0 -> rdword (aview tfibsegs H mem) (bp - 16) = Some nfp0 -> 4096 <= ra0 ->
(if bp + 16 <? ly_top ly
then (if bad_next bp (ly_top ly) nfp0 then ch = [] else bp + 16 <= nfp0 /\ fpchain (rdword (aview tfibsegs H mem)) nfp0 (ly_top ly) ch)
else ch = []) ->
SRr tfibsegs W (mkCfg (mkst regs (Z_to_bv 64 DM_UNW_PC) mem (seg_rom tfibsegs)) md)
(dm_unw_post W regs mem md this bp
(if bp <=? ly_bot ly then [pc0] else if bp + 16 <? ly_top ly then unwind_of_chain pc0 ((bp, ra0, nfp0) :: ch) else [pc0])).
Proof.
intros U1 W ly regs mem md this pc0 bp ra0 nfp0 ch H m sp T.
intros LY IMG R10 R11 R12 R13 R14 R15 R4 Hra Hpc0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 P10 V11 V12
Hsp16 Hsplo Pstk Hthis8 Hthislo Hthis_sp Pthis Hthis_bp Hsp_bp Hbp_hi Hbp8 Hra0 Hnfp0 Hra4096 Hch.
destruct (Z.leb_spec bp (ly_bot ly)) as [Hb|Hb].
- exact (dm_unwind_bot W ly regs mem md this pc0 bp LY IMG R10 R11 R12 R13 R14 R15 R4 Hra Hpc0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 P10 V11 V12
Hsp16 Hsplo Pstk Hthis8 Hthislo Hthis_sp Pthis Hthis_bp Hsp_bp Hb Hbp_hi Hbp8).
- exact (U1 W ly regs mem md this pc0 bp ra0 nfp0 ch LY IMG R10 R11 R12 R13 R14 R15 R4 Hra Hpc0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 P10 V11 V12
Hsp16 Hsplo Pstk Hthis8 Hthislo Hthis_sp Pthis Hthis_bp Hsp_bp Hb Hbp_hi Hbp8 Hra0 Hnfp0 Hra4096 Hch).
Qed.
End c.
