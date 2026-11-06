(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the contract and walk of ctrl_finish on fuzz_grant.asan, written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v, proofs/cgif/cgif_file_fuzzer/lib/YC20.v. *)
(* Modified by Theorem Labs, 2026-10: rcs_val_mem1_of_chunk and rcs_aview_of_eq copied from lib/A/Prog/CtrlFinish.v's val_mem1_of_chunk and aview_of_eq (a working branch 5aae1e8a0ce, cgif-adapted; rcs_aview_of_eq fixes its H to w_H W); the rest written new for image B. *)
(* Image B (fuzz_grant.asan-ubsan, bin/ sha256 fde52226dc48, symbols 5a5ee7c02b4e): the walk of
   reac_ctrl_record_cksum_stamp 0x82694 (listing offset 0x1c58), whose contract is
   lib/B/Prog/GrantBContracts.v:808-836. The call sums the n - 1 bytes r[0..n-1) and stores
   (- sum) mod 128 at r + n - 1 (lib/Prog/RcRec.v stampck); for n = 1 the branch at 0x826b0 skips
   the loop and the stored byte is 0.

   The loop's trip count n - 1 is symbolic, so the walk is four symbolic runs, not one:
     entry   0x82694 .. 0x826c8   (two shapes: the n = 1 skip, and the loop set-up for 2 <= n)
     body    0x826c8 .. 0x82704   one pass, with the back edge 0x82704 -> 0x826c8 as a second run
     last    0x826c8 .. 0x82720   the pass that leaves the loop (a7 = 1)
     tail    0x82720 .. ret       the store of the stamp and the return
   Each run starts from a symbolic state re-abstracted over the machine state the run before it
   left: the atoms are 32 the running pointer, 33 the running sum, 34 the shadow base, 35 the
   remaining count, 36 / 37 the two temporaries, 38 the byte the pass reads and 39..42 the dead
   registers of the tail. The loop runs by induction on the remaining count.

   The trap guards (0x826c8, 0x826d4, 0x826d8, 0x82720, 0x82730, 0x82734 -> unimp 0x82760) and the
   two report branches (0x82714 load1, 0x82770 store1) are refuted by the executor from the atom
   facts, the condition p >=u r and the shadow premises: the in-code check
   `lb s, shadow(x); bnez s; andi t, x, 7; blt t, s` is the engine's token form, so each pass
   leaves the single obligation `range_addressable ... (r + i) 1`, discharged from the contract's
   range_addressable over [r, r + n).

   Written new for image B: image A has no reac_ctrl_record_cksum_stamp symbol (it inlines the function into
   ctrl_finish), so there is no image-A walk of it. *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation Znumtheory.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s YI00 YI16.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import YCbq.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0s YM05.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import PaRun PaShadow PaStep.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import PaJournal PaBase.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import
GrantSyms GrantList GrantPa GrantPaLib GrantTop GrantBContracts.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require RcModel RcRec.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the one piece of arithmetic the code needs: negw; andi 127 ---------------------------- *)
Lemma rcs_ul : forall z, bv_unsigned (Z_to_bv 64 z) = z mod 2 ^ 64.
Proof. intros z. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). reflexivity. Qed.
Lemma rcs_mod128_64 : forall s, (s mod 2 ^ 64) mod 128 = s mod 128.
Proof. intros s. symmetry. apply Zmod_div_mod; [lia | lia | exists (2 ^ 57); reflexivity]. Qed.
Lemma rcs_swrap32_mod128 : forall x, bv_swrap 32 x mod 128 = x mod 128.
Proof.
intros x. unfold bv_swrap. change (bv_half_modulus 32) with 2147483648.
unfold bv_wrap. change (bv_modulus 32) with 4294967296.
Z.div_mod_to_equations. lia.
Qed.
Lemma rcs_stamp_val : forall s,
Z.land (bv_unsigned (Z_to_bv 64 (bv_swrap 32 (0 - bv_unsigned (Z_to_bv 64 s))))) 127 = (- s) mod 128.
Proof.
intros s. rewrite !rcs_ul. change 127 with (Z.ones 7). rewrite Z.land_ones by lia.
change (2 ^ 7) with 128. rewrite rcs_mod128_64, rcs_swrap32_mod128.
rewrite (Zminus_mod 0 (s mod 2 ^ 64) 128), rcs_mod128_64, <- (Zminus_mod 0 s 128).
f_equal; lia.
Qed.
Lemma rcs_psum_range : forall (bs : list byte) (i : nat), 0 <= RcModel.psum bs i <= 255 * Z.of_nat i.
Proof.
intros bs i. induction i as [|i IH]; cbn [RcModel.psum]; [lia|].
pose proof (bv_unsigned_in_range 8 (nth i bs (Z_to_bv 8 0))) as Hr.
change (bv_modulus 8) with 256 in Hr. lia.
Qed.
Lemma rcs_psum_S : forall (bs : list byte) (i : nat),
RcModel.psum bs (S i) = RcModel.psum bs i + bv_unsigned (nth i bs (Z_to_bv 8 0)).
Proof. reflexivity. Qed.

(* ---- regs_ok from its 32 cases --------------------------------------------------------------- *)
Lemma rcs_regs_ok_32 : forall (E : env) (sr : list sv) (rc0 : bvmap 5 word),
nth 0 sr (SLit 0) = SLit 0 ->
(forall i : nat, (i < 32)%nat -> getr rc0 (Z_to_bv 5 (Z.of_nat i)) = sv_denot E (nth i sr (SLit 0))) ->
regs_ok E sr rc0.
Proof.
intros E sr rc0 H0 H rr. unfold sr_get, ridx.
pose proof (u5_range rr) as Hr.
destruct (bv_eqb rr 0) eqn:Hz.
- apply bv_eqb_eq in Hz. subst rr. reflexivity.
- specialize (H (Z.to_nat (bv_unsigned rr)) ltac:(lia)).
  replace (Z_to_bv 5 (Z.of_nat (Z.to_nat (bv_unsigned rr)))) with rr in H
    by (rewrite Z2Nat.id by lia; symmetry; apply Z_to_bv_bv_unsigned).
  exact H.
Qed.

Section W.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {PI : PAImg grant_listing}.
#[local] Notation SEGS := (@pa_segs _ grant_listing PI).
#[local] Notation VAL := (@pa_val _ grant_listing PI).
#[local] Notation BASE := (@pa_val _ grant_listing PI A_TEXT).
Variable B : asyms.

(* the four points of image B's code, as listing offsets *)
Definition RCS_ENT : Z := AF_reac_ctrl_record_cksum_stamp.          (* 0x82694 *)
Definition RCS_LOOP : Z := AF_reac_ctrl_record_cksum_stamp + 0x34.  (* 0x826c8 *)
Definition RCS_JMP : Z := AF_reac_ctrl_record_cksum_stamp + 0x70.   (* 0x82704 *)
Definition RCS_TAIL : Z := AF_reac_ctrl_record_cksum_stamp + 0x8c.  (* 0x82720 *)
Definition RCS_STK : Z := 16.
Definition RCS_Bx : sv := SOff 34 0.
Definition RCS_span : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
Definition RCS_HI : Z := 2 ^ 47 - 1.
Definition RCS_SH : list shent := [mkSHE 32 0 1].

(* the regions: the 16-byte frame (with the saved ra once it is written), the byte the pass reads,
   and the byte the tail writes *)
Definition rcs_stk0 : YP09.region := YP09.mkRegion (Some 2%nat) (-16) 0 (-16) 0 [].
Definition rcs_stk : YP09.region :=
  YP09.mkRegion (Some 2%nat) (-16) 0 0 0 [YP09.mkChunk (-8) (CVal 8 (SOff 1 0))].
Definition rcs_rdb : YP09.region :=
  YP09.mkRegion (Some 32%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 38 0))].
Definition rcs_wrb : YP09.region := YP09.mkRegion (Some 32%nat) 0 1 0 1 [].

(* the atoms above the registers: 32 p, 33 sum, 34 shadow base, 35 count, 36 t0, 37 t1, 38 byte,
   39..42 the tail's dead a4..a7 *)
Definition rcs_ext (p sum cnt bt : Z) (vt0 vt1 v14 v15 v16 v17 : word) : list word :=
  [Z_to_bv 64 p; Z_to_bv 64 sum; Z_to_bv 64 SHADOW_OFF; Z_to_bv 64 cnt; vt0; vt1;
   Z_to_bv 64 bt; v14; v15; v16; v17].

Definition rcs_eregs : list sv :=
  [SLit 0; SOff 1 0; SOff 2 0; SOff 3 0; SOff 4 0; SOff 5 0; SOff 6 0; SOff 7 0;
   SOff 8 0; SOff 9 0; SOff 10 0; SOff 11 0; SOff 12 0; SOff 13 0; SOff 14 0; SOff 15 0;
   SOff 16 0; SOff 17 0; SOff 18 0; SOff 19 0; SOff 20 0; SOff 21 0; SOff 22 0; SOff 23 0;
   SOff 24 0; SOff 25 0; SOff 26 0; SOff 27 0; SOff 28 0; SOff 29 0; SOff 30 0; SOff 31 0].
Definition rcs_eregs1 : list sv :=
  [SLit 0; SOff 1 0; SOff 2 0; SOff 3 0; SOff 4 0; SOff 5 0; SOff 6 0; SOff 7 0;
   SOff 8 0; SOff 9 0; SOff 10 0; SLit 1; SOff 12 0; SOff 13 0; SOff 14 0; SOff 15 0;
   SOff 16 0; SOff 17 0; SOff 18 0; SOff 19 0; SOff 20 0; SOff 21 0; SOff 22 0; SOff 23 0;
   SOff 24 0; SOff 25 0; SOff 26 0; SOff 27 0; SOff 28 0; SOff 29 0; SOff 30 0; SOff 31 0].
Definition rcs_lregs (a7 : sv) : list sv :=
  [SLit 0; SOff 1 0; SOff 2 (-16); SOff 3 0; SOff 4 0; SOff 36 0; SOff 37 0; SOff 7 0;
   SOff 8 0; SOff 9 0; SOff 10 0; SOff 32 0; SOff 33 0; SOff 34 0; SOff 11 (-1); SLit 1;
   SOff 32 0; a7; SOff 18 0; SOff 19 0; SOff 20 0; SOff 21 0; SOff 22 0; SOff 23 0;
   SOff 24 0; SOff 25 0; SOff 26 0; SOff 27 0; SOff 28 0; SOff 29 0; SOff 30 0; SOff 31 0].
Definition rcs_tregs : list sv :=
  [SLit 0; SOff 1 0; SOff 2 (-16); SOff 3 0; SOff 4 0; SOff 36 0; SOff 37 0; SOff 7 0;
   SOff 8 0; SOff 9 0; SOff 10 0; SOff 32 0; SOff 33 0; SOff 34 0; SOff 39 0; SOff 40 0;
   SOff 41 0; SOff 42 0; SOff 18 0; SOff 19 0; SOff 20 0; SOff 21 0; SOff 22 0; SOff 23 0;
   SOff 24 0; SOff 25 0; SOff 26 0; SOff 27 0; SOff 28 0; SOff 29 0; SOff 30 0; SOff 31 0].

(* the registers every run leaves alone: ra, gp, tp, t2, s0, s1, a0 and s2..s11 / t3..t6 *)
Definition RCS_KEEPL : list (bv 5) :=
  [1; 3; 4; 7; 8; 9; 10; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.

Definition rcs_efacts (nlo nhi : Z) : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (10%nat, mkAF 1 RCS_HI 0);
           (11%nat, mkAF nlo nhi 0); (34%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] [].
Definition rcs_lfacts (clo chi : Z) : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (10%nat, mkAF 1 RCS_HI 0); (11%nat, mkAF 2 RCS_HI 0);
           (32%nat, mkAF 1 RCS_HI 0); (33%nat, mkAF 0 (2 ^ 62) 0);
           (34%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (35%nat, mkAF clo chi 0); (38%nat, mkAF 0 255 0)]
          [mkAC BC_GEU (SOff 32 0) (SOff 10 0)] [].
Definition rcs_tfacts : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (10%nat, mkAF 1 RCS_HI 0);
           (32%nat, mkAF 1 RCS_HI 0); (33%nat, mkAF 0 (2 ^ 62) 0);
           (34%nat, mkAF SHADOW_OFF SHADOW_OFF 0)]
          [mkAC BC_GEU (SOff 32 0) (SOff 10 0)] [].

Definition ss_ent : sstate :=
  mkSS RCS_ENT rcs_eregs [rcs_stk0; got_regionP; bcell_regionP 34] None (rcs_efacts 2 RCS_HI).
Definition ss_ent1 : sstate :=
  mkSS RCS_ENT rcs_eregs1 [rcs_stk0; got_regionP; bcell_regionP 34] None (rcs_efacts 1 1).
Definition ss_body : sstate :=
  mkSS RCS_LOOP (rcs_lregs (SOff 35 0)) [rcs_rdb] None (rcs_lfacts 2 RCS_HI).
Definition ss_last : sstate :=
  mkSS RCS_LOOP (rcs_lregs (SLit 1)) [rcs_rdb] None (rcs_lfacts 1 1).
Definition ss_tail : sstate :=
  mkSS RCS_TAIL rcs_tregs [rcs_stk; rcs_wrb] None rcs_tfacts.

Section H.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_grant) (PI := PI).

(* ---- the premises of the contract, once ------------------------------------------------------ *)
Section C.
Variables (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world SEGS).
Variables (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)).
Variables (lyc : alayout) (Sc : astate) (W : world SEGS) (memc : word -> option byte) (mdc : Model).
Variables (k : Z) (regs : bvmap 5 word) (r n : Z) (RS : list byte).
Hypothesis HJ0 : ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k.
Hypothesis Hra : YK0s.ret_ok (getr regs 1).
Hypothesis Hra4 : 4096 <= raZ regs.
Hypothesis Hgp : getr regs 3 = w64 (as_gp B).
Hypothesis Htp : getr regs 4 = w64 (as_tp B).
Hypothesis H10 : getr regs 10 = w64 r.
Hypothesis H11 : getr regs 11 = w64 n.
Hypothesis Hal16 : spZ regs mod 16 = 0.
Hypothesis Hwlo : sp0 - STK <= spZ regs - RCS_STK.
Hypothesis Hwhi : spZ regs <= sp0.
Hypothesis Hn1 : 1 <= n.
Hypothesis Hlen : Z.of_nat (length RS) = n - 1.
Hypothesis HGB : garr8 SEGS (mrestrict (w_H W) memc) r (map bv_unsigned RS).
Hypothesis Hr0 : 0 < r.
Hypothesis Hamem : amem_range r n.
Hypothesis Himg : r + n <= IMG_LO_B \/ IMG_TOP_B <= r.
Hypothesis Hpsp : spZ regs <= r \/ r + n <= spZ regs - RCS_STK.
Hypothesis HWR : twr_ok B STK sp0 FP ly S lyc Sc own W memc (spZ regs) (r + n - 1) 1.
Hypothesis HRA : range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF r n.

(* the numeric facts the states need *)
Lemma rcs_bounds :
0 < r /\ r + n <= RCS_HI /\ 2 ^ 46 <= spZ regs <= 2 ^ 47 /\ spZ regs mod 16 = 0 /\ 0 <= raZ regs < 2 ^ 64.
Proof.
pose proof HJ0 as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _ & _).
pose proof Hstk as (Hal & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof alloc_ceiling_val as HAC.
pose proof (u64_range (getr regs 1)) as Hu1.
unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hamem.
unfold RCS_HI, RCS_STK, raZ in *.
repeat split; lia.
Qed.

(* what every run leaves of the memory: the frame is the only thing it may touch *)
Definition RCS_mem (mem : word -> option byte) : Prop :=
(forall x : word, ~ (spZ regs - 16 <= bv_unsigned x < spZ regs) ->
   mrestrict (w_H W) mem x = mrestrict (w_H W) memc x) /\
mem_grows (mrestrict (w_H W) memc) (mrestrict (w_H W) mem) /\
YI04.val_mem SEGS (mrestrict (w_H W) mem) (spZ regs - 8) 8 (raZ regs).

Definition RE (ext : list word) : env := Eimg (Ereg regs ext).

Lemma rcs_ew_lo : forall ext (i : nat) (rr : bv 5),
(i < 32)%nat -> Z.of_nat i = bv_unsigned rr -> ew (RE ext) i = getr regs rr.
Proof.
intros ext i rr Hi Hr. unfold RE. rewrite Eimg_low by (unfold A_TEXT; lia).
apply ew_Ereg_nat. exact Hr.
Qed.
Lemma rcs_ew_hi : forall ext (i j : nat),
i = (32 + j)%nat -> (j < 200)%nat -> ew (RE ext) i = nth j ext (Z_to_bv 64 0).
Proof.
intros ext i j Hi Hj. subst i. unfold RE. rewrite Eimg_low by (unfold A_TEXT; cbn; lia).
apply ew_Ereg_extra.
Qed.
Lemma rcs_ew_obj : forall ext (m : nat), (m < 271)%nat -> ew (RE ext) (A_OBJ m) = Z_to_bv 64 (VAL (A_OBJ m)).
Proof. intros ext m Hm. unfold RE. apply Eimg_img. unfold A_OBJ, A_TEXT, A_LIM. lia. Qed.
Lemma rcs_env : forall ext, img_env VAL A_LIM (RE ext).
Proof. intros ext. unfold RE. apply Eimg_env. Qed.
Lemma rcs_agree : forall ext, env_agree 32 (Ereg regs ext) (RE ext).
Proof. intros ext. split; [intros nn Hnn; unfold RE; apply Eimg_low; unfold A_TEXT; lia | reflexivity]. Qed.
Lemma rcs_denot_keep : forall ext (i : nat) (rr : bv 5) (rc0 : bvmap 5 word),
(i < 32)%nat -> Z.of_nat i = bv_unsigned rr -> getr rc0 rr = getr regs rr ->
getr rc0 rr = sv_denot (RE ext) (SOff i 0).
Proof.
intros ext i rr rc0 Hi Hr Hk. cbn [sv_denot].
rewrite (rcs_ew_lo ext i rr Hi Hr), Z.add_0_r, Z_to_bv_bv_unsigned. exact Hk.
Qed.
Lemma rcs_denot_lo : forall ext (i j : nat) (v : Z),
i = (32 + j)%nat -> (j < 200)%nat -> nth j ext (Z_to_bv 64 0) = Z_to_bv 64 v ->
sv_denot (RE ext) (SOff i 0) = Z_to_bv 64 (v mod 2 ^ 64).
Proof.
intros ext i j v Hi Hj Hv. cbn [sv_denot]. rewrite (rcs_ew_hi ext i j Hi Hj), Hv, Z.add_0_r, rcs_ul. reflexivity.
Qed.

(* mbyte and val_mem move between memories that agree at the address *)
Lemma rcs_mbyte_eq : forall (m m' : word -> option byte) (a : Z),
m' (Z_to_bv 64 a) = m (Z_to_bv 64 a) -> YP09.mbyte SEGS m' a = YP09.mbyte SEGS m a.
Proof. intros m m' a Hq. unfold YP09.mbyte. rewrite Hq. reflexivity. Qed.
Lemma rcs_val1_tr : forall (m m' : word -> option byte) (a v : Z),
m' (Z_to_bv 64 a) = m (Z_to_bv 64 a) -> YI04.val_mem SEGS m a 1 v -> YI04.val_mem SEGS m' a 1 v.
Proof.
intros m m' a v Hq H kk Hk. assert (Hk0 : kk = 0%nat) by lia. subst kk.
cbn [Z.of_nat]. rewrite Z.add_0_r. rewrite (rcs_mbyte_eq m m' a Hq).
pose proof (H 0%nat ltac:(lia)) as Hz. cbn [Z.of_nat] in Hz. rewrite Z.add_0_r in Hz. exact Hz.
Qed.
Lemma rcs_aview_tr : forall (m m' : word -> option byte) (a : Z),
mrestrict (w_H W) m' (Z_to_bv 64 a) = mrestrict (w_H W) m (Z_to_bv 64 a) ->
aview SEGS (w_H W) m' a = aview SEGS (w_H W) m a.
Proof. intros m m' a Hq. unfold aview. rewrite (rcs_mbyte_eq _ _ a Hq). reflexivity. Qed.

(* the record's bytes, as the states need them *)
Lemma rcs_byte_val : forall (j : nat), (j < length RS)%nat ->
YI04.val_mem SEGS (mrestrict (w_H W) memc) (r + Z.of_nat j) 1 (bv_unsigned (nth j RS (Z_to_bv 8 0))).
Proof.
intros j Hj. destruct (HGB j ltac:(rewrite length_map; lia)) as [Hv _].
rewrite (nth_indep (map bv_unsigned RS) 0 (bv_unsigned (Z_to_bv 8 0))) in Hv by (rewrite length_map; lia).
rewrite (map_nth bv_unsigned RS (Z_to_bv 8 0) j) in Hv. exact Hv.
Qed.
Lemma rcs_byte_rng : forall (j : nat), 0 <= bv_unsigned (nth j RS (Z_to_bv 8 0)) < 256.
Proof.
intros j. pose proof (bv_unsigned_in_range 8 (nth j RS (Z_to_bv 8 0))) as Hr.
change (bv_modulus 8) with 256 in Hr. lia.
Qed.
(* the record lies outside the frame window *)
Lemma rcs_rec_apart : forall (a : Z), r <= a < r + n -> ~ (spZ regs - 16 <= a < spZ regs).
Proof. intros a Ha. unfold RCS_STK in Hpsp. lia. Qed.

(* ---- the entry state ------------------------------------------------------------------------ *)
Lemma rcs_eregs_eq : rcs_eregs = sr_atoms.
Proof. vm_compute. reflexivity. Qed.
Lemma rcs_eregs1_eq : rcs_eregs1 = sr_set sr_atoms 11%bv (SLit 1).
Proof. vm_compute. reflexivity. Qed.

Lemma rcs_ent_ok : forall (sr : list sv) (nlo nhi : Z) (ext : list word),
nth 2 ext (Z_to_bv 64 0) = Z_to_bv 64 SHADOW_OFF ->
regs_ok (RE ext) sr regs -> nlo <= n <= nhi ->
st_ok_pi SEGS VAL (RE ext)
  (mkSS RCS_ENT sr [stack_region 16; got_regionP; bcell_regionP 34] None (rcs_efacts nlo nhi))
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + RCS_ENT)) memc (seg_rom SEGS))).
Proof.
intros sr nlo nhi ext Hsb Hregs Hnb.
pose proof rcs_bounds as (Hr0' & Hrn & Hsp46 & Hspal & Hrau).
unfold RCS_HI in Hrn.
pose proof HJ0 as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _ & _).
pose proof Hstk as (Hal & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof alloc_ceiling_val as HAC.
pose proof IMG_LO_B_val as HLO. pose proof IMG_TOP_B_val as HTOP.
pose proof (pa_obj_img 1%nat ltac:(lia)) as HgotR.
pose proof (pa_obj_img 35%nat ltac:(lia)) as HcelR.
pose proof (pal_got_cell B TL) as HgcD.
destruct (al_const _ _ LAWS lyc Sc W memc mdc HAR) as (Kcell & _ & Kgot & _).
rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
assert (E2 : ew (RE ext) 2%nat = getr regs 2) by (apply (rcs_ew_lo ext 2%nat 2%bv); [lia | reflexivity]).
assert (E10 : ew (RE ext) 10%nat = getr regs 10) by (apply (rcs_ew_lo ext 10%nat 10%bv); [lia | reflexivity]).
assert (E11 : ew (RE ext) 11%nat = getr regs 11) by (apply (rcs_ew_lo ext 11%nat 11%bv); [lia | reflexivity]).
assert (E34 : ew (RE ext) 34%nat = Z_to_bv 64 SHADOW_OFF)
  by (rewrite (rcs_ew_hi ext 34%nat 2%nat eq_refl ltac:(lia)); exact Hsb).
assert (Eg1 : ew (RE ext) (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1))) by (apply rcs_ew_obj; lia).
assert (Eg35 : ew (RE ext) (A_OBJ 35) = Z_to_bv 64 (VAL (A_OBJ 35))) by (apply rcs_ew_obj; lia).
assert (Usp : bv_unsigned (ew (RE ext) 2%nat) = spZ regs) by (rewrite E2; reflexivity).
assert (U10 : bv_unsigned (ew (RE ext) 10%nat) = r) by (rewrite E10, H10; apply unsigned_lit_small; lia).
assert (U11 : bv_unsigned (ew (RE ext) 11%nat) = n) by (rewrite E11, H11; apply unsigned_lit_small; lia).
assert (U34 : bv_unsigned (ew (RE ext) 34%nat) = SHADOW_OFF)
  by (rewrite E34; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (Ug1 : base_val (RE ext) (Some (A_OBJ 1)) = VAL (A_OBJ 1))
  by (cbn [base_val]; rewrite Eg1; apply unsigned_lit_small; pose proof (pa_val_range (A_OBJ 1)); lia).
assert (Ug35 : base_val (RE ext) (Some (A_OBJ 35)) = VAL (A_OBJ 35))
  by (cbn [base_val]; rewrite Eg35; apply unsigned_lit_small; pose proof (pa_val_range (A_OBJ 35)); lia).
rewrite restrict_mkst_fx. unfold RCS_ENT. apply pa_entry_st_ok_full.
- exact Hregs.
- vm_compute. reflexivity.
- unfold stack_region, got_regionP, bcell_regionP.
  repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  + cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable SEGS). apply Hpres. unfold RCS_STK in Hwlo. lia.
  + rewrite Ug1. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS (RE ext) _ (VAL (A_OBJ 1)) 0 8 (SOff (A_OBJ 35) 0) (VAL (A_OBJ 35)));
    [cbn [sv_denot]; rewrite Eg35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | pose proof (pa_val_range (A_OBJ 35)); zside | zside |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) memc _ _ Kgot).
  + rewrite Ug35. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS (RE ext) _ (VAL (A_OBJ 35)) 0 8 (SOff 34%nat 0) SHADOW_OFF);
    [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | unfold SHADOW_OFF; zside | zside |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) memc _ _ Kcell).
- apply pairwise_disjoint_of_extents.
  unfold stack_region, got_regionP, bcell_regionP, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite Ug1, Ug35. cbn [base_val]. rewrite Usp.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  revert HgotR HcelR HgcD Hsp46 HLO HTOP. clear. intros. repeat split; lia.
- split; [|split; [exact I | exact I]].
  unfold rcs_efacts. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite Usp, U10, U11, U34. change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
  unfold RCS_HI, SHADOW_OFF in *.
  repeat match goal with |- _ /\ _ => split end; try exact I; lia.
Qed.

(* ---- the loop-head state --------------------------------------------------------------------- *)
Definition rcs_lext (p sum cnt bt : Z) (vt0 vt1 : word) : list word :=
  rcs_ext p sum cnt bt vt0 vt1 (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0).

Lemma rcs_cond_ok : forall (ext : list word) (p' : Z),
nth 0 ext (Z_to_bv 64 0) = Z_to_bv 64 p' -> 0 <= p' < 2 ^ 64 -> r <= p' ->
acond_ok (RE ext) (mkAC BC_GEU (SOff 32 0) (SOff 10 0)).
Proof.
intros ext p' Hp Hpr Hle. pose proof rcs_bounds as (Hr0' & Hrn & _). unfold RCS_HI in Hrn.
unfold acond_ok. cbn [ac_c ac_a ac_b sv_denot Sem.branch_taken].
rewrite (rcs_ew_hi ext 32%nat 0%nat eq_refl ltac:(lia)), Hp.
rewrite (rcs_ew_lo ext 10%nat 10%bv ltac:(lia) ltac:(reflexivity)), H10.
unfold w64. rewrite !Z.add_0_r, !unsigned_lit_small by lia.
unfold bv_ltu. rewrite !unsigned_lit_small by lia.
replace (p' <? r) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.

Lemma rcs_stk_ok : forall (ext : list word) (mem : word -> option byte),
RCS_mem mem -> region_ok SEGS (RE ext) (mrestrict (w_H W) mem) rcs_stk.
Proof.
intros ext mem (HMa & HMg & HMr).
pose proof rcs_bounds as (Hr0' & Hrn & Hsp46 & Hspal & Hrau).
assert (Usp : base_val (RE ext) (Some 2%nat) = spZ regs)
  by (cbn [base_val]; rewrite (rcs_ew_lo ext 2%nat 2%bv ltac:(lia) ltac:(reflexivity)); reflexivity).
unfold rcs_stk, region_ok.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
rewrite Usp. split; [lia|]. split; [lia|]. split.
- intros o Ho. lia.
- constructor; [|constructor].
  apply (chunk_ok_val SEGS (RE ext) _ (spZ regs) (-8) 8 (SOff 1 0) (raZ regs)).
  + cbn [sv_denot]. rewrite (rcs_ew_lo ext 1%nat 1%bv ltac:(lia) ltac:(reflexivity)).
    unfold raZ. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
  + zside.
  + zside.
  + cbn [N.to_nat]. exact HMr.
Qed.

Lemma rcs_loop_ok : forall (ms : machine_state) (a7sv : sv) (clo chi p sum cnt bt : Z) (vt0 vt1 : word),
ms = mkst (ms_regs ms) (Z_to_bv 64 (BASE + RCS_LOOP)) (ms_mem ms) (seg_rom SEGS) ->
RCS_mem (ms_mem ms) ->
(forall rr : bv 5, In rr RCS_KEEPL -> getr (ms_regs ms) rr = getr regs rr) ->
getr (ms_regs ms) 2 = w64 (spZ regs - 16) ->
getr (ms_regs ms) 5 = vt0 -> getr (ms_regs ms) 6 = vt1 ->
getr (ms_regs ms) 11 = w64 p -> getr (ms_regs ms) 12 = w64 sum ->
getr (ms_regs ms) 13 = w64 SHADOW_OFF -> getr (ms_regs ms) 14 = w64 (n - 1) ->
getr (ms_regs ms) 15 = w64 1 -> getr (ms_regs ms) 16 = w64 p ->
getr (ms_regs ms) 17 = sv_denot (RE (rcs_lext p sum cnt bt vt0 vt1)) a7sv ->
2 <= n -> r <= p -> p + 1 <= r + n -> 0 <= sum <= 2 ^ 62 -> clo <= cnt <= chi -> 0 <= cnt <= RCS_HI ->
0 <= bt < 256 ->
YI04.val_mem SEGS (mrestrict (w_H W) (ms_mem ms)) p 1 bt ->
st_ok_pi SEGS VAL (RE (rcs_lext p sum cnt bt vt0 vt1))
  (mkSS RCS_LOOP (rcs_lregs a7sv) [rcs_rdb] None (rcs_lfacts clo chi))
  (restrict (w_H W) ms).
Proof.
intros ms a7sv clo chi p sum cnt bt vt0 vt1 Hms HM HK R2 R5 R6 R11 R12 R13 R14 R15 R16 R17
  Hn2 Hrp Hpn Hsum Hcnt Hcntb Hbt Hval.
unfold RCS_HI in Hcntb.
pose proof rcs_bounds as (Hr0' & Hrn & Hsp46 & Hspal & Hrau). unfold RCS_HI in Hrn.
set (ext := rcs_lext p sum cnt bt vt0 vt1) in *.
assert (Hx0 : nth 0 ext (Z_to_bv 64 0) = Z_to_bv 64 p) by reflexivity.
assert (Hx1 : nth 1 ext (Z_to_bv 64 0) = Z_to_bv 64 sum) by reflexivity.
assert (Hx2 : nth 2 ext (Z_to_bv 64 0) = Z_to_bv 64 SHADOW_OFF) by reflexivity.
assert (Hx3 : nth 3 ext (Z_to_bv 64 0) = Z_to_bv 64 cnt) by reflexivity.
assert (Hx4 : nth 4 ext (Z_to_bv 64 0) = vt0) by reflexivity.
assert (Hx5 : nth 5 ext (Z_to_bv 64 0) = vt1) by reflexivity.
assert (Hx6 : nth 6 ext (Z_to_bv 64 0) = Z_to_bv 64 bt) by reflexivity.
assert (E32 : ew (RE ext) 32%nat = Z_to_bv 64 p)
  by (rewrite (rcs_ew_hi ext 32%nat 0%nat eq_refl ltac:(lia)); exact Hx0).
assert (E33 : ew (RE ext) 33%nat = Z_to_bv 64 sum)
  by (rewrite (rcs_ew_hi ext 33%nat 1%nat eq_refl ltac:(lia)); exact Hx1).
assert (E34 : ew (RE ext) 34%nat = Z_to_bv 64 SHADOW_OFF)
  by (rewrite (rcs_ew_hi ext 34%nat 2%nat eq_refl ltac:(lia)); exact Hx2).
assert (E35 : ew (RE ext) 35%nat = Z_to_bv 64 cnt)
  by (rewrite (rcs_ew_hi ext 35%nat 3%nat eq_refl ltac:(lia)); exact Hx3).
assert (E36 : ew (RE ext) 36%nat = vt0)
  by (rewrite (rcs_ew_hi ext 36%nat 4%nat eq_refl ltac:(lia)); exact Hx4).
assert (E37 : ew (RE ext) 37%nat = vt1)
  by (rewrite (rcs_ew_hi ext 37%nat 5%nat eq_refl ltac:(lia)); exact Hx5).
assert (E38 : ew (RE ext) 38%nat = Z_to_bv 64 bt)
  by (rewrite (rcs_ew_hi ext 38%nat 6%nat eq_refl ltac:(lia)); exact Hx6).
assert (E2 : ew (RE ext) 2%nat = getr regs 2) by (apply (rcs_ew_lo ext 2%nat 2%bv); [lia | reflexivity]).
assert (E1 : ew (RE ext) 1%nat = getr regs 1) by (apply (rcs_ew_lo ext 1%nat 1%bv); [lia | reflexivity]).
assert (E10 : ew (RE ext) 10%nat = getr regs 10) by (apply (rcs_ew_lo ext 10%nat 10%bv); [lia | reflexivity]).
assert (E11 : ew (RE ext) 11%nat = getr regs 11) by (apply (rcs_ew_lo ext 11%nat 11%bv); [lia | reflexivity]).
assert (Usp : bv_unsigned (ew (RE ext) 2%nat) = spZ regs) by (rewrite E2; reflexivity).
assert (U10 : bv_unsigned (ew (RE ext) 10%nat) = r) by (rewrite E10, H10; apply unsigned_lit_small; lia).
assert (U11 : bv_unsigned (ew (RE ext) 11%nat) = n) by (rewrite E11, H11; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew (RE ext) 32%nat) = p) by (rewrite E32; apply unsigned_lit_small; lia).
assert (U33 : bv_unsigned (ew (RE ext) 33%nat) = sum) by (rewrite E33; apply unsigned_lit_small; lia).
assert (U34 : bv_unsigned (ew (RE ext) 34%nat) = SHADOW_OFF)
  by (rewrite E34; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U35 : bv_unsigned (ew (RE ext) 35%nat) = cnt) by (rewrite E35; apply unsigned_lit_small; lia).
assert (U38 : bv_unsigned (ew (RE ext) 38%nat) = bt) by (rewrite E38; apply unsigned_lit_small; lia).
pose proof HM as (HMa & HMg & HMr).
rewrite Hms at 1. rewrite restrict_mkst_fx. unfold RCS_LOOP. apply pa_entry_st_ok_full.
- (* regs_ok *)
  regs_ok_cases_pre ltac:(
    solve
    [ reflexivity
    | eapply rcs_denot_keep; [lia | reflexivity | apply HK; cbv [RCS_KEEPL In]; repeat (first [left; reflexivity | right])]
    | rewrite R2; cbn [sv_denot]; rewrite E2; unfold w64, spZ; f_equal; lia
    | rewrite R5; cbn [sv_denot]; rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | rewrite R6; cbn [sv_denot]; rewrite E37, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | rewrite R11; cbn [sv_denot]; rewrite E32, Z.add_0_r, unsigned_lit_small by lia; reflexivity
    | rewrite R12; cbn [sv_denot]; rewrite E33, Z.add_0_r, unsigned_lit_small by lia; reflexivity
    | rewrite R13; cbn [sv_denot]; rewrite E34, Z.add_0_r, unsigned_lit_small by (unfold SHADOW_OFF; lia); reflexivity
    | rewrite R14; cbn [sv_denot]; rewrite E11, H11; unfold w64;
      rewrite unsigned_lit_small by lia; f_equal; lia
    | rewrite R15; reflexivity
    | rewrite R16; cbn [sv_denot]; rewrite E32, Z.add_0_r, unsigned_lit_small by lia; reflexivity
    | exact R17 ]).
- vm_compute. reflexivity.
- unfold rcs_rdb. repeat apply Forall_cons; try apply Forall_nil.
  + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    cbn [base_val]. rewrite U32. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS (RE ext) _ p 0 1 (SOff 38%nat 0) bt);
    [cbn [sv_denot]; rewrite E38, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
    cbn [N.to_nat]. rewrite Z.add_0_r. exact Hval.
- cbn [pairwise_disjoint all_disjoint]. split; exact I.
- split; [|split; [|exact I]].
  + unfold rcs_lfacts. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp, U10, U11, U32, U33, U34, U35, U38.
    change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
    unfold RCS_HI, SHADOW_OFF in *.
    repeat match goal with |- _ /\ _ => split end; try exact I; lia.
  + unfold rcs_lfacts. cbn [f_conds conds_ok]. split; [|exact I].
    apply (rcs_cond_ok ext p Hx0 ltac:(lia) Hrp).
Qed.

(* ---- the tail state -------------------------------------------------------------------------- *)
Definition rcs_text (lastp sum : Z) (vt0 vt1 v14 v15 v16 v17 : word) : list word :=
  rcs_ext lastp sum 0 0 vt0 vt1 v14 v15 v16 v17.

Lemma rcs_shadow_lo : forall (x : Z), r <= x < r + n ->
~ (spZ regs - 16 <= bv_unsigned (Z_to_bv 64 (shadow_of_addr SHADOW_OFF x)) < spZ regs).
Proof.
intros x Hx. pose proof rcs_bounds as (Hr0' & Hrn & Hsp46 & _). unfold RCS_HI in Hrn.
unfold shadow_of_addr, SHADOW_OFF.
assert (Hd : 0 <= x / 8 <= 2 ^ 44) by (Z.div_mod_to_equations; lia).
rewrite unsigned_lit_small by lia. lia.
Qed.
Lemma rcs_ra_tr : forall (mem : word -> option byte) (a len : Z),
RCS_mem mem -> r <= a -> a + len <= r + n ->
range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF a len.
Proof.
intros mem a len HM Ha Hb. destruct HM as (HMa & _ & _).
intros x Hx. destruct (HRA x ltac:(lia)) as (sv' & Hsv & Hok). exists sv'. split; [|exact Hok].
rewrite <- Hsv. apply rcs_aview_tr. apply HMa. apply rcs_shadow_lo. lia.
Qed.

Lemma rcs_tail_ok : forall (ms : machine_state) (lastp sum : Z) (vt0 vt1 v14 v15 v16 v17 : word),
ms = mkst (ms_regs ms) (Z_to_bv 64 (BASE + RCS_TAIL)) (ms_mem ms) (seg_rom SEGS) ->
RCS_mem (ms_mem ms) ->
(forall rr : bv 5, In rr RCS_KEEPL -> getr (ms_regs ms) rr = getr regs rr) ->
getr (ms_regs ms) 2 = w64 (spZ regs - 16) ->
getr (ms_regs ms) 5 = vt0 -> getr (ms_regs ms) 6 = vt1 ->
getr (ms_regs ms) 11 = w64 lastp -> getr (ms_regs ms) 12 = w64 sum ->
getr (ms_regs ms) 13 = w64 SHADOW_OFF ->
getr (ms_regs ms) 14 = v14 -> getr (ms_regs ms) 15 = v15 ->
getr (ms_regs ms) 16 = v16 -> getr (ms_regs ms) 17 = v17 ->
lastp = r + n - 1 -> 0 <= sum <= 2 ^ 62 ->
st_ok_pi SEGS VAL (RE (rcs_text lastp sum vt0 vt1 v14 v15 v16 v17)) ss_tail (restrict (w_H W) ms)
/\ sh_ok SEGS RCS_Bx RCS_SH (RE (rcs_text lastp sum vt0 vt1 v14 v15 v16 v17))
     (mrestrict (w_H W) (ms_mem ms)).
Proof.
intros ms lastp sum vt0 vt1 v14 v15 v16 v17 Hms HM HK R2 R5 R6 R11 R12 R13 R14 R15 R16 R17 Hlp Hsum.
pose proof rcs_bounds as (Hr0' & Hrn & Hsp46 & Hspal & Hrau). unfold RCS_HI in Hrn.
set (ext := rcs_text lastp sum vt0 vt1 v14 v15 v16 v17) in *.
assert (Hx0 : nth 0 ext (Z_to_bv 64 0) = Z_to_bv 64 lastp) by reflexivity.
assert (Hx1 : nth 1 ext (Z_to_bv 64 0) = Z_to_bv 64 sum) by reflexivity.
assert (Hx2 : nth 2 ext (Z_to_bv 64 0) = Z_to_bv 64 SHADOW_OFF) by reflexivity.
assert (E32 : ew (RE ext) 32%nat = Z_to_bv 64 lastp)
  by (rewrite (rcs_ew_hi ext 32%nat 0%nat eq_refl ltac:(lia)); exact Hx0).
assert (E33 : ew (RE ext) 33%nat = Z_to_bv 64 sum)
  by (rewrite (rcs_ew_hi ext 33%nat 1%nat eq_refl ltac:(lia)); exact Hx1).
assert (E34 : ew (RE ext) 34%nat = Z_to_bv 64 SHADOW_OFF)
  by (rewrite (rcs_ew_hi ext 34%nat 2%nat eq_refl ltac:(lia)); exact Hx2).
assert (E36 : ew (RE ext) 36%nat = vt0) by (rewrite (rcs_ew_hi ext 36%nat 4%nat eq_refl ltac:(lia)); reflexivity).
assert (E37 : ew (RE ext) 37%nat = vt1) by (rewrite (rcs_ew_hi ext 37%nat 5%nat eq_refl ltac:(lia)); reflexivity).
assert (E39 : ew (RE ext) 39%nat = v14) by (rewrite (rcs_ew_hi ext 39%nat 7%nat eq_refl ltac:(lia)); reflexivity).
assert (E40 : ew (RE ext) 40%nat = v15) by (rewrite (rcs_ew_hi ext 40%nat 8%nat eq_refl ltac:(lia)); reflexivity).
assert (E41 : ew (RE ext) 41%nat = v16) by (rewrite (rcs_ew_hi ext 41%nat 9%nat eq_refl ltac:(lia)); reflexivity).
assert (E42 : ew (RE ext) 42%nat = v17) by (rewrite (rcs_ew_hi ext 42%nat 10%nat eq_refl ltac:(lia)); reflexivity).
assert (E2 : ew (RE ext) 2%nat = getr regs 2) by (apply (rcs_ew_lo ext 2%nat 2%bv); [lia | reflexivity]).
assert (E1 : ew (RE ext) 1%nat = getr regs 1) by (apply (rcs_ew_lo ext 1%nat 1%bv); [lia | reflexivity]).
assert (E10 : ew (RE ext) 10%nat = getr regs 10) by (apply (rcs_ew_lo ext 10%nat 10%bv); [lia | reflexivity]).
assert (Usp : bv_unsigned (ew (RE ext) 2%nat) = spZ regs) by (rewrite E2; reflexivity).
assert (U10 : bv_unsigned (ew (RE ext) 10%nat) = r) by (rewrite E10, H10; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew (RE ext) 32%nat) = lastp) by (rewrite E32; apply unsigned_lit_small; lia).
assert (U33 : bv_unsigned (ew (RE ext) 33%nat) = sum) by (rewrite E33; apply unsigned_lit_small; lia).
assert (U34 : bv_unsigned (ew (RE ext) 34%nat) = SHADOW_OFF)
  by (rewrite E34; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
pose proof HM as (HMa & HMg & HMr).
assert (Hpr : apresent (w_H W) (ms_mem ms) lastp).
{ apply (apresent_grows (w_H W) memc (ms_mem ms) lastp HMg).
  exact (proj1 (proj2 (HWR lastp ltac:(lia)))). }
split.
- rewrite Hms at 1. rewrite restrict_mkst_fx. unfold ss_tail, RCS_TAIL. apply pa_entry_st_ok_full.
  + regs_ok_cases_pre ltac:(
      solve
      [ reflexivity
      | eapply rcs_denot_keep; [lia | reflexivity | apply HK; cbv [RCS_KEEPL In]; repeat (first [left; reflexivity | right])]
      | rewrite R2; cbn [sv_denot]; rewrite E2; unfold w64, spZ; f_equal; lia
      | rewrite R5; cbn [sv_denot]; rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | rewrite R6; cbn [sv_denot]; rewrite E37, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | rewrite R11; cbn [sv_denot]; rewrite E32, Z.add_0_r, unsigned_lit_small by lia; reflexivity
      | rewrite R12; cbn [sv_denot]; rewrite E33, Z.add_0_r, unsigned_lit_small by lia; reflexivity
      | rewrite R13; cbn [sv_denot]; rewrite E34, Z.add_0_r, unsigned_lit_small by (unfold SHADOW_OFF; lia); reflexivity
      | rewrite R14; cbn [sv_denot]; rewrite E39, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | rewrite R15; cbn [sv_denot]; rewrite E40, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | rewrite R16; cbn [sv_denot]; rewrite E41, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | rewrite R17; cbn [sv_denot]; rewrite E42, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity ]).
  + vm_compute. reflexivity.
  + unfold rcs_wrb. repeat apply Forall_cons; try apply Forall_nil.
    * apply rcs_stk_ok. exact HM.
    * unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
      cbn [base_val]. rewrite U32. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS).
      replace (lastp + o) with lastp by lia. exact Hpr.
  + apply pairwise_disjoint_of_extents.
    unfold rcs_stk, rcs_wrb, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. cbn [base_val]. rewrite U32, Usp.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold RCS_STK in Hpsp.
    assert (Hd : spZ regs <= lastp \/ lastp + 1 <= spZ regs - 16) by (destruct Hpsp as [Hq|Hq]; lia).
    destruct Hd as [Hd|Hd]; (revert Hd Hsp46 Hr0' Hrn Hlp; clear; intros; repeat split; lia).
  + split; [|split; [|exact I]].
    * unfold rcs_tfacts. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite Usp, U10, U32, U33, U34.
      change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
      unfold RCS_HI, SHADOW_OFF in *.
      repeat match goal with |- _ /\ _ => split end; try exact I; lia.
    * unfold rcs_tfacts. cbn [f_conds conds_ok]. split; [|exact I].
      apply (rcs_cond_ok ext lastp Hx0 ltac:(lia) ltac:(lia)).
- unfold sh_ok, RCS_SH. constructor; [|constructor].
  apply (shent_ok_of_range SEGS (w_H W) (ms_mem ms) (RE ext) RCS_Bx 32%nat lastp 1 lastp 0 1).
  + apply (rcs_ra_tr (ms_mem ms) lastp 1 HM ltac:(lia) ltac:(lia)).
  + unfold U, RCS_Bx. cbn [sv_denot]. rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned.
    apply unsigned_lit_small. unfold SHADOW_OFF. lia.
  + unfold U. cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned.
    apply unsigned_lit_small. lia.
  + lia.
  + lia.
  + intros x Hx. change (Z.min 0 1) with 0 in Hx. change (Z.max 0 1) with 1 in Hx.
    unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd, SHADOW_OFF in *. lia.
Qed.

(* ---- the tail run: the store of the stamp, and the return ----------------------------------- *)
Lemma rcs_mod128_32 : forall s, (s mod 2 ^ 32) mod 128 = s mod 128.
Proof. intros s. symmetry. apply Zmod_div_mod; [lia | lia | exists (2 ^ 25); reflexivity]. Qed.
Lemma rcs_land127 : forall x, 0 <= x -> Z.land x 127 = x mod 128.
Proof. intros x Hx. change 127 with (Z.ones 7). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma rcs_land_zcanon : forall Y, zcanon (Z.land (zcanon Y) 127) = Y mod 128.
Proof.
intros Y. unfold zcanon, M64.
rewrite (rcs_land127 (Y mod 2 ^ 64) ltac:(pose proof (Z.mod_pos_bound Y (2 ^ 64) ltac:(lia)); lia)).
rewrite rcs_mod128_64.
pose proof (Z.mod_pos_bound Y 128 ltac:(lia)) as Hm. apply Z.mod_small. lia.
Qed.
Definition RCS_STAMPSV : sv := SAlu ALU_AND (SAluw ALU_SUB (SLit 0) (SOff 33 0)) (SLit 127).
Lemma rcs_stampsv_val : forall (E : env) (sum : Z),
0 <= sum < 2 ^ 62 -> U E (SOff 33 0) = sum ->
sv_denot E RCS_STAMPSV = Z_to_bv 64 ((- sum) mod 128).
Proof.
intros E sum Hsum H33. unfold RCS_STAMPSV. rewrite denot_lit_U. f_equal.
rewrite U_SAlu, (U_SLit E 127), U_of_S, S_SAluw, (U_SLit E 0), H33.
cbn [zalu_raw]. change (zcanon 0) with 0. change (zcanon 127) with 127.
rewrite rcs_land_zcanon, rcs_swrap32_mod128.
change (0 mod 2 ^ 32) with 0.
rewrite (Zminus_mod 0 (sum mod 2 ^ 32) 128), rcs_mod128_32, <- (Zminus_mod 0 sum 128).
f_equal; lia.
Qed.
Lemma rcs_val_mem1_of_chunk : forall (Ez : env) (m : word -> option byte) (q off : Z) (e : sv) (z : Z),
YP09.chunk_ok SEGS Ez m q (YP09.mkChunk off (CVal 1 e)) -> sv_denot Ez e = Z_to_bv 64 z ->
YI04.val_mem SEGS m (q + off) 1%nat (z mod 256).
Proof.
intros Ez m q off e z Hc Hz kk Hk.
assert (Hk0 : kk = 0%nat) by lia. subst kk.
destruct (Hc 0 ltac:(cbn; lia)) as (bb & Hb1 & Hb2).
cbn [YP09.cbyte YP09.c_off YP09.c_val] in Hb1, Hb2. injection Hb1 as <-.
rewrite !Z.add_0_r in Hb2. cbn [Z.of_nat]. rewrite Z.add_0_r. rewrite Hb2. f_equal.
unfold YP09.byte_of_word. rewrite Hz, Z_to_bv_unsigned.
apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 8) with 256. change (bv_modulus 64) with (2 ^ 64).
unfold YO0f.le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
change (2 ^ 8) with 256. rewrite !Z.shiftr_0_r. rewrite !Z.mod_mod by lia.
symmetry. apply Zmod_div_mod; [lia | lia | exists (2 ^ 56); reflexivity].
Qed.
Lemma rcs_aview_of_eq : forall (m m' : word -> option byte) (a : Z),
mrestrict (w_H W) m' (Z_to_bv 64 a) = mrestrict (w_H W) m (Z_to_bv 64 a) ->
aview SEGS (w_H W) m' a = aview SEGS (w_H W) m a.
Proof. intros m m' a Hq. unfold aview, YP09.mbyte. rewrite Hq. reflexivity. Qed.

Lemma rcs_tail_done : forall (ms : machine_state) (md : Model) (lastp sum : Z)
  (vt0 vt1 v14 v15 v16 v17 : word),
ms = mkst (ms_regs ms) (Z_to_bv 64 (BASE + RCS_TAIL)) (ms_mem ms) (seg_rom SEGS) ->
RCS_mem (ms_mem ms) ->
(forall rr : bv 5, In rr RCS_KEEPL -> getr (ms_regs ms) rr = getr regs rr) ->
getr (ms_regs ms) 2 = w64 (spZ regs - 16) ->
getr (ms_regs ms) 5 = vt0 -> getr (ms_regs ms) 6 = vt1 ->
getr (ms_regs ms) 11 = w64 lastp -> getr (ms_regs ms) 12 = w64 sum ->
getr (ms_regs ms) 13 = w64 SHADOW_OFF ->
getr (ms_regs ms) 14 = v14 -> getr (ms_regs ms) 15 = v15 ->
getr (ms_regs ms) 16 = v16 -> getr (ms_regs ms) 17 = v17 ->
lastp = r + n - 1 -> sum = RcModel.psum RS (length RS) ->
ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (ms_mem ms) md k ->
SRr SEGS W (mkCfg ms md)
  (tb_reac_ctrl_record_cksum_stamp_post B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs r n RS).
Proof.
intros ms md lastp sum vt0 vt1 v14 v15 v16 v17 Hms HM HK R2 R5 R6 R11 R12 R13 R14 R15 R16 R17
  Hlp Hsum HJ.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
pose proof rcs_bounds as (Hr0' & Hrn & Hsp46 & Hspal & Hrau). unfold RCS_HI in Hrn.
pose proof alloc_ceiling_val as HAC.
pose proof IMG_LO_B_val as HLO. pose proof IMG_TOP_B_val as HTOP.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HJ0 as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HpresC & Hstk & _ & _).
pose proof Hstk as (Hal & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
assert (Hsumb : 0 <= sum < 2 ^ 62).
{ pose proof (rcs_psum_range RS (length RS)) as Hps. rewrite Hsum. lia. }
destruct (rcs_tail_ok ms lastp sum vt0 vt1 v14 v15 v16 v17 Hms HM HK R2 R5 R6 R11 R12 R13 R14 R15 R16 R17
  Hlp ltac:(lia)) as [HS SHOK].
set (ext := rcs_text lastp sum vt0 vt1 v14 v15 v16 v17) in *.
assert (HEI : img_env VAL A_LIM (RE ext)) by apply rcs_env.
assert (HAE : env_agree 32 (Ereg regs ext) (RE ext)) by apply rcs_agree.
assert (E1 : ew (RE ext) 1%nat = getr regs 1) by (apply (rcs_ew_lo ext 1%nat 1%bv); [lia | reflexivity]).
assert (E2 : ew (RE ext) 2%nat = getr regs 2) by (apply (rcs_ew_lo ext 2%nat 2%bv); [lia | reflexivity]).
assert (E32 : ew (RE ext) 32%nat = Z_to_bv 64 lastp)
  by (rewrite (rcs_ew_hi ext 32%nat 0%nat eq_refl ltac:(lia)); reflexivity).
assert (E33 : ew (RE ext) 33%nat = Z_to_bv 64 sum)
  by (rewrite (rcs_ew_hi ext 33%nat 1%nat eq_refl ltac:(lia)); reflexivity).
assert (Usp : bv_unsigned (ew (RE ext) 2%nat) = spZ regs) by (rewrite E2; reflexivity).
assert (U32 : bv_unsigned (ew (RE ext) 32%nat) = lastp) by (rewrite E32; apply unsigned_lit_small; lia).
pose proof HM as (HMa & HMg & HMr).
paj_run_tok RUN HS HJ SHOK RCS_span.
- unfold ss_tail, rcs_stk, rcs_wrb. cbn [ss_mem].
  apply awr_ok_cons_ro; [cbn; lia|].
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 32%nat lastp);
  [reflexivity | exact U32 | cbn [YP09.r_wlo YP09.r_whi] | apply awr_ok_nil].
  intros aa Haa. exact (proj1 (HWR aa ltac:(lia))).
- lazymatch goal with
  | HS' : st_ok_pi _ _ ?Ez ?ssx (restrict _ ?msy), HJz : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
    pose proof (st_ok_mem_ok SEGS Ez (abs_ss VAL ssx) (restrict (w_H W) msy) HS') as HMO;
    cbn [abs_ss setpc ss_mem restrict ms_mem] in HMO;
    destruct HMO as (_ & HMO & _);
    let l := eval vm_compute in (ss_mem ssx) in change (ss_mem ssx) with l in HMO;
    apply Forall_inv_tail in HMO; apply Forall_inv in HMO;
    destruct HMO as (_ & _ & _ & HCH);
    cbn [YP09.r_base] in HCH;
    assert (Hb32 : base_val Ez (Some 32%nat) = lastp)
      by (cbn [base_val]; rewrite ?ew_ewset_other by lia; exact U32);
    rewrite Hb32 in HCH;
    pose proof (Forall_inv HCH) as Hcst;
    cbn [YP09.c_off YP09.c_val] in Hcst;
    assert (Eb33 : U Ez (SOff 33%nat 0) = sum)
      by (apply U_atom; [rewrite ?ew_ewset_other by lia; exact E33 | lia]);
    prreg HS' (1%bv : bv 5) RR1;
    eapply (RET W _ _ _ _ _ HS' eq_refl ltac:(vm_compute; reflexivity));
    let mq := fresh "mat" in intros mq
  end.
  lazymatch goal with
  | HFr' : frame_of _ _ (mrestrict _ _) (mrestrict _ ?mm) |- _ =>
    assert (HM2 : forall x : word, ~ (spZ regs - 16 <= bv_unsigned x < spZ regs) ->
             bv_unsigned x <> lastp -> mrestrict (w_H W) mm x = mrestrict (w_H W) memc x)
    by (intros xx Ha Hb; rewrite (HFr' xx); [apply HMa; exact Ha|];
        intros (rr & Hrr & Hbb);
        let l := eval vm_compute in (ss_mem ss_tail) in change (ss_mem ss_tail) with l in Hrr;
        cbn [In] in Hrr; repeat (destruct Hrr as [Hrr | Hrr]); try (exfalso; exact Hrr); subst rr;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val] in Hbb;
        rewrite ?ew_ewset_other in Hbb by lia; rewrite ?Usp, ?U32 in Hbb; lia)
  end.
  split; [reflexivity|].
  lazymatch goal with
  | HS' : st_ok_pi _ _ ?Ez ?ssx (restrict _ ?msy), HJz : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
    HG' : mem_grows _ _, Hcst : YP09.chunk_ok _ _ _ _ _, HM2 : forall x : word, _ |- _ =>
    exists (ms_regs msy), (ms_mem msy); eexists;
    split; [cbn [ms_regs]; rewrite RR1; cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia;
            rewrite E1, Hra; reflexivity|];
    split; [cbn [ms_mem]; apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJz|];
    split; [eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ regs ext HS');
            [eapply env_agree_trans; [exact HAE | split;
               [intros nn Hnn; rewrite ?ew_ewset_other by lia; reflexivity | reflexivity]]
            | vm_compute; reflexivity]|];
    split;
    [ (* the record and its stamp *)
      intros j Hj; rewrite length_map, length_app in Hj; cbn [length] in Hj;
      rewrite (nth_indep (map bv_unsigned (RS ++ [Z_to_bv 8 (RcRec.stampck RS)])) 0
                 (bv_unsigned (Z_to_bv 8 0))) by (rewrite length_map, length_app; cbn [length]; lia);
      rewrite (map_nth bv_unsigned _ (Z_to_bv 8 0) j);
      destruct (Nat.lt_ge_cases j (length RS)) as [Hjl|Hjg];
      [ rewrite app_nth1 by lia; split; [|apply rcs_byte_rng];
        apply (rcs_val1_tr (mrestrict (w_H W) memc));
        [ apply HM2; rewrite unsigned_lit_small by lia; [apply rcs_rec_apart; lia | lia]
        | apply rcs_byte_val; lia ]
      | assert (Hje : j = length RS) by lia; subst j;
        rewrite app_nth2 by lia; rewrite Nat.sub_diag; cbn [nth];
        pose proof (rcs_val_mem1_of_chunk Ez (mrestrict (w_H W) (ms_mem msy)) lastp 0 RCS_STAMPSV
          ((- sum) mod 128) Hcst (rcs_stampsv_val Ez sum ltac:(lia) Eb33)) as Hvs;
        pose proof (Z.mod_pos_bound (- sum) 128 ltac:(lia)) as Hmb;
        rewrite (Z.mod_small ((- sum) mod 128) 256) in Hvs by lia;
        assert (Hst : RcRec.stampck RS = (- sum) mod 128)
          by (unfold RcRec.stampck; rewrite Hsum; reflexivity);
        rewrite Hst; rewrite Z_to_bv_unsigned; unfold bv_wrap;
        change (bv_modulus 8) with 256; rewrite (Z.mod_small ((- sum) mod 128) 256) by lia;
        split; [|lia];
        replace (r + Z.of_nat (length RS)) with (lastp + 0) by lia; exact Hvs ]
    | ]
  end.
  (* tcj_kept *)
  unfold tcj_kept, STK_reac_ctrl_record_cksum_stamp.
  split; [intros aa Haa Hww Hee; apply rcs_aview_of_eq; apply HM2;
          rewrite unsigned_lit_small by lia; lia |].
  split; [intros bb mm ii Hin Hii Hee;
          destruct (al_blocks _ _ LAWS lyc Sc W memc mdc bb mm HAR Hin) as (_ & Hb4096 & Hbceil & _);
          apply rcs_aview_of_eq; apply HM2; rewrite unsigned_lit_small by lia; unfold RCS_STK in Hwlo; lia |].
  split; [intros aa Hin _ _; pose proof (pa_img_range aa Hin) as Hir;
          apply rcs_aview_of_eq; apply HM2; rewrite unsigned_lit_small by lia; lia |].
  split; [intros cid pos aa Hin Hrr Hee;
          destruct (frames_bounds SEGS B LAWS lyc Sc W memc mdc cid pos HAR Hin) as (Hf0 & Hfc & _);
          pose proof (fs_frame_bytes_nonneg cid) as Hfb;
          pose proof (shadow_addr_bounds (frame_addr lyc cid pos) ltac:(lia)) as [Hs1a Hs1b];
          pose proof (shadow_addr_bounds (frame_addr lyc cid pos + fs_frame_bytes cid) ltac:(lia))
            as [Hs2a Hs2b];
          specialize (Hs2b ltac:(lia));
          pose proof (shadow_range_end (frame_addr lyc cid pos) (fs_frame_bytes cid) Hfb) as Hs3;
          unfold in_zr, frame_rng in Hrr; cbn [fst snd] in Hrr;
          set (qq := fs_frame_bytes cid / 8) in *;
          unfold SHADOW_OFF in Hs1a, Hs2a;
          unfold RCS_STK in Hwlo; destruct Hrr as [Hrr|Hrr];
          apply rcs_aview_of_eq; apply HM2; rewrite unsigned_lit_small by lia; lia |].
  split; [intros aa _ _ Hpr;
          lazymatch goal with HG' : mem_grows _ (mrestrict _ ?mm) |- _ =>
            exact (apresent_grows (w_H W) memc mm aa (mem_grows_trans _ _ _ HMg HG') Hpr) end |].
  intros aa Haa.
  lazymatch goal with HJz : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
    pose proof HJz as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _);
    apply Hpres2; unfold RCS_STK in Hwlo; lia
  end.
Qed.

(* ---- the loop, by induction on the remaining count ------------------------------------------ *)
Lemma rcs_val_tr8 : forall (m m' : word -> option byte) (a v : Z),
(forall x : word, m' x = m x) -> YI04.val_mem SEGS m a 8 v -> YI04.val_mem SEGS m' a 8 v.
Proof.
intros m m' a v Heq H kk Hk. rewrite (rcs_mbyte_eq m m' (a + Z.of_nat kk) (Heq _)). apply H. exact Hk.
Qed.
Lemma rcs_mem_step : forall (m m' : word -> option byte),
RCS_mem m -> (forall x : word, mrestrict (w_H W) m' x = mrestrict (w_H W) m x) ->
mem_grows (mrestrict (w_H W) m) (mrestrict (w_H W) m') -> RCS_mem m'.
Proof.
intros m m' (HMa & HMg & HMr) Heq Hgr. split; [|split].
- intros x Hx. rewrite Heq. apply HMa. exact Hx.
- eapply mem_grows_trans; [exact HMg | exact Hgr].
- apply (rcs_val_tr8 (mrestrict (w_H W) m)); [exact Heq | exact HMr].
Qed.
Lemma rcs_byte_cur : forall (mem : word -> option byte) (i : nat),
RCS_mem mem -> (i < length RS)%nat ->
YI04.val_mem SEGS (mrestrict (w_H W) mem) (r + Z.of_nat i) 1 (bv_unsigned (nth i RS (Z_to_bv 8 0))).
Proof.
intros mem i HM Hi. destruct HM as (HMa & _ & _).
apply (rcs_val1_tr (mrestrict (w_H W) memc)).
- apply HMa. rewrite unsigned_lit_small.
  + apply rcs_rec_apart. lia.
  + pose proof rcs_bounds as (Hr0' & Hrn & _). unfold RCS_HI in Hrn. lia.
- apply rcs_byte_val. exact Hi.
Qed.

Lemma rcs_loop : forall (m i : nat) (ms : machine_state) (md : Model),
(i + m = length RS)%nat -> (0 < m)%nat -> 2 <= n ->
ms = mkst (ms_regs ms) (Z_to_bv 64 (BASE + RCS_LOOP)) (ms_mem ms) (seg_rom SEGS) ->
RCS_mem (ms_mem ms) ->
(forall rr : bv 5, In rr RCS_KEEPL -> getr (ms_regs ms) rr = getr regs rr) ->
getr (ms_regs ms) 2 = w64 (spZ regs - 16) ->
getr (ms_regs ms) 11 = w64 (r + Z.of_nat i) ->
getr (ms_regs ms) 12 = w64 (RcModel.psum RS i) ->
getr (ms_regs ms) 13 = w64 SHADOW_OFF ->
getr (ms_regs ms) 14 = w64 (n - 1) ->
getr (ms_regs ms) 15 = w64 1 ->
getr (ms_regs ms) 16 = w64 (r + Z.of_nat i) ->
getr (ms_regs ms) 17 = w64 (Z.of_nat m) ->
ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (ms_mem ms) md k ->
SRr SEGS W (mkCfg ms md)
  (tb_reac_ctrl_record_cksum_stamp_post B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs r n RS).
Proof.
induction m as [|m' IH]; intros i ms md Hik Hm0 Hn2 Hms HM HK R2 R11 R12 R13 R14 R15 R16 R17 HJ; [lia|].
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
pose proof rcs_bounds as (Hr0' & Hrn & Hsp46 & Hspal & Hrau). unfold RCS_HI in Hrn.
pose proof (rcs_psum_range RS i) as Hpsi.
set (p := r + Z.of_nat i) in *.
set (bt := bv_unsigned (nth i RS (Z_to_bv 8 0))) in *.
pose proof (rcs_byte_rng i) as Hbtr. fold bt in Hbtr.
assert (Hil : (i < length RS)%nat) by lia.
assert (Hpr : r <= p) by (unfold p; lia).
assert (Hpn : p + 1 <= r + n) by (unfold p; lia).
assert (Hval : YI04.val_mem SEGS (mrestrict (w_H W) (ms_mem ms)) p 1 bt)
  by (apply rcs_byte_cur; [exact HM | exact Hil]).
destruct m' as [|m''].
- (* the pass that leaves the loop *)
  set (ext := rcs_lext p (RcModel.psum RS i) 1 bt (getr (ms_regs ms) 5) (getr (ms_regs ms) 6)) in *.
  assert (HS : st_ok_pi SEGS VAL (RE ext) ss_last (restrict (w_H W) ms)).
  { unfold ss_last. apply (rcs_loop_ok ms (SLit 1) 1 1 p (RcModel.psum RS i) 1 bt
      (getr (ms_regs ms) 5) (getr (ms_regs ms) 6) Hms HM HK R2 eq_refl eq_refl R11 R12 R13 R14 R15 R16);
    try (unfold RCS_HI; lia).
    - rewrite R17. reflexivity.
    - exact Hval. }
  assert (SHOK : sh_ok SEGS RCS_Bx [] (RE ext) (mrestrict (w_H W) (ms_mem ms))) by constructor.
  assert (HEI : img_env VAL A_LIM (RE ext)) by apply rcs_env.
  assert (HAE : env_agree 32 (Ereg regs ext) (RE ext)) by apply rcs_agree.
  assert (E2 : ew (RE ext) 2%nat = getr regs 2) by (apply (rcs_ew_lo ext 2%nat 2%bv); [lia | reflexivity]).
  assert (E10 : ew (RE ext) 10%nat = getr regs 10) by (apply (rcs_ew_lo ext 10%nat 10%bv); [lia | reflexivity]).
  assert (E11 : ew (RE ext) 11%nat = getr regs 11) by (apply (rcs_ew_lo ext 11%nat 11%bv); [lia | reflexivity]).
  assert (E32 : ew (RE ext) 32%nat = Z_to_bv 64 p)
    by (rewrite (rcs_ew_hi ext 32%nat 0%nat eq_refl ltac:(lia)); reflexivity).
  assert (E33 : ew (RE ext) 33%nat = Z_to_bv 64 (RcModel.psum RS i))
    by (rewrite (rcs_ew_hi ext 33%nat 1%nat eq_refl ltac:(lia)); reflexivity).
  assert (E34 : ew (RE ext) 34%nat = Z_to_bv 64 SHADOW_OFF)
    by (rewrite (rcs_ew_hi ext 34%nat 2%nat eq_refl ltac:(lia)); reflexivity).
  assert (E38 : ew (RE ext) 38%nat = Z_to_bv 64 bt)
    by (rewrite (rcs_ew_hi ext 38%nat 6%nat eq_refl ltac:(lia)); reflexivity).
  paj_run_to_tok RUNTO HS HJ SHOK RCS_span RCS_TAIL.
  + (* the shadow byte the pass needs *)
    srr_obls. unfold RCS_Bx. rewrite <- (aview_rd_of SEGS).
    rewrite (U_atom (RE ext) 34%nat SHADOW_OFF E34 ltac:(unfold SHADOW_OFF; lia)).
    rewrite (U_atom (RE ext) 32%nat p E32 ltac:(lia)).
    apply (rcs_ra_tr (ms_mem ms) p 1 HM); lia.
  + unfold ss_last. cbn [ss_mem]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil.
  + lazymatch goal with
    | HS2 : st_ok_pi _ _ ?Ez ?ssx (restrict _ ?msy), HJ2 : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
      HFr2 : frame_of _ _ (mrestrict _ _) (mrestrict _ _), HG2 : mem_grows _ _ |- _ =>
      assert (Hmm : forall x : word, mrestrict (w_H W) (ms_mem msy) x = mrestrict (w_H W) (ms_mem ms) x)
        by (intros xx; apply HFr2; intros (rr & Hrr & Hbb);
            let l := eval vm_compute in (ss_mem ss_last) in change (ss_mem ss_last) with l in Hrr;
            cbn [In] in Hrr; repeat (destruct Hrr as [Hrr | Hrr]); try (exfalso; exact Hrr); subst rr;
            cbn [YP09.r_wlo YP09.r_whi] in Hbb; lia);
      assert (HM2 : RCS_mem (ms_mem msy)) by (apply (rcs_mem_step (ms_mem ms)); assumption);
      assert (HK2 : forall rr : bv 5, In rr RCS_KEEPL -> getr (ms_regs msy) rr = getr regs rr)
        by (apply (regs_kept_of_st_ok_pi Ez ssx (restrict (w_H W) msy) regs ext RCS_KEEPL HS2);
            [eapply env_agree_trans; [exact HAE | split;
               [intros nn Hnn; rewrite ?ew_ewset_other by lia; reflexivity | reflexivity]]
            | vm_compute; reflexivity]);
      prreg HS2 (2%bv : bv 5) Q2; prreg HS2 (5%bv : bv 5) Q5; prreg HS2 (6%bv : bv 5) Q6;
      prreg HS2 (11%bv : bv 5) Q11; prreg HS2 (12%bv : bv 5) Q12; prreg HS2 (13%bv : bv 5) Q13;
      prreg HS2 (14%bv : bv 5) Q14; prreg HS2 (15%bv : bv 5) Q15; prreg HS2 (16%bv : bv 5) Q16;
      prreg HS2 (17%bv : bv 5) Q17;
      rewrite ?ew_ewset_other in Q2, Q5, Q6, Q11, Q12, Q13, Q14, Q15, Q16, Q17 by lia;
      apply (rcs_tail_done msy _ (r + n - 1) (RcModel.psum RS (length RS))
               (getr (ms_regs msy) 5) (getr (ms_regs msy) 6) (getr (ms_regs msy) 14)
               (getr (ms_regs msy) 15) (getr (ms_regs msy) 16) (getr (ms_regs msy) 17));
      [ exact (st_ok_pi_restrict_mkst (w_H W) Ez ssx msy HS2 eq_refl)
      | exact HM2 | exact HK2
      | rewrite Q2, E2; unfold w64, spZ; f_equal; lia
      | reflexivity | reflexivity
      | rewrite Q11, E10, E11, H10, H11; unfold w64; rewrite !unsigned_lit_small by lia;
        rewrite (alu_add_small (r + -1) n) by (unfold M64; lia); f_equal; lia
      | rewrite Q12, E33, E38; rewrite (alu_add_small (RcModel.psum RS i) bt) by (unfold M64; lia);
        unfold w64; f_equal; replace (length RS) with (Datatypes.S i) by lia; rewrite rcs_psum_S; reflexivity
      | rewrite Q13, E34; reflexivity
      | reflexivity | reflexivity | reflexivity | reflexivity
      | reflexivity | reflexivity | exact HJ2 ]
    end.
- (* a pass that goes round again *)
  set (ext := rcs_lext p (RcModel.psum RS i) (Z.of_nat (Datatypes.S (Datatypes.S m''))) bt
                (getr (ms_regs ms) 5) (getr (ms_regs ms) 6)) in *.
  assert (HS : st_ok_pi SEGS VAL (RE ext) ss_body (restrict (w_H W) ms)).
  { unfold ss_body. apply (rcs_loop_ok ms (SOff 35 0) 2 RCS_HI p (RcModel.psum RS i)
      (Z.of_nat (Datatypes.S (Datatypes.S m''))) bt (getr (ms_regs ms) 5) (getr (ms_regs ms) 6)
      Hms HM HK R2 eq_refl eq_refl R11 R12 R13 R14 R15 R16);
    try (unfold RCS_HI; lia).
    - fold ext. rewrite R17, (rcs_denot_lo ext 35%nat 3%nat (Z.of_nat (Datatypes.S (Datatypes.S m'')))
        eq_refl ltac:(lia) eq_refl).
      unfold w64. f_equal. symmetry. apply Z.mod_small. lia.
    - exact Hval. }
  assert (SHOK : sh_ok SEGS RCS_Bx [] (RE ext) (mrestrict (w_H W) (ms_mem ms))) by constructor.
  assert (HEI : img_env VAL A_LIM (RE ext)) by apply rcs_env.
  assert (HAE : env_agree 32 (Ereg regs ext) (RE ext)) by apply rcs_agree.
  assert (E2 : ew (RE ext) 2%nat = getr regs 2) by (apply (rcs_ew_lo ext 2%nat 2%bv); [lia | reflexivity]).
  assert (E11 : ew (RE ext) 11%nat = getr regs 11) by (apply (rcs_ew_lo ext 11%nat 11%bv); [lia | reflexivity]).
  assert (E32 : ew (RE ext) 32%nat = Z_to_bv 64 p)
    by (rewrite (rcs_ew_hi ext 32%nat 0%nat eq_refl ltac:(lia)); reflexivity).
  assert (E33 : ew (RE ext) 33%nat = Z_to_bv 64 (RcModel.psum RS i))
    by (rewrite (rcs_ew_hi ext 33%nat 1%nat eq_refl ltac:(lia)); reflexivity).
  assert (E34 : ew (RE ext) 34%nat = Z_to_bv 64 SHADOW_OFF)
    by (rewrite (rcs_ew_hi ext 34%nat 2%nat eq_refl ltac:(lia)); reflexivity).
  assert (E35 : ew (RE ext) 35%nat = Z_to_bv 64 (Z.of_nat (Datatypes.S (Datatypes.S m''))))
    by (rewrite (rcs_ew_hi ext 35%nat 3%nat eq_refl ltac:(lia)); reflexivity).
  assert (E38 : ew (RE ext) 38%nat = Z_to_bv 64 bt)
    by (rewrite (rcs_ew_hi ext 38%nat 6%nat eq_refl ltac:(lia)); reflexivity).
  paj_run_to_tok RUNTO HS HJ SHOK RCS_span RCS_JMP.
  + srr_obls. unfold RCS_Bx. rewrite <- (aview_rd_of SEGS).
    rewrite (U_atom (RE ext) 34%nat SHADOW_OFF E34 ltac:(unfold SHADOW_OFF; lia)).
    rewrite (U_atom (RE ext) 32%nat p E32 ltac:(lia)).
    apply (rcs_ra_tr (ms_mem ms) p 1 HM); lia.
  + unfold ss_body. cbn [ss_mem]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil.
  + (* one more instruction: the back edge *)
    lazymatch goal with
    | HS2 : st_ok_pi _ _ ?Ez ?ssx (restrict _ ?msy), HJ2 : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
      SH2 : sh_ok _ _ _ _ _, HFr2 : frame_of _ _ (mrestrict _ _) (mrestrict _ _), HG2 : mem_grows _ _ |- _ =>
      assert (Hmm : forall x : word, mrestrict (w_H W) (ms_mem msy) x = mrestrict (w_H W) (ms_mem ms) x)
        by (intros xx; apply HFr2; intros (rr & Hrr & Hbb);
            let l := eval vm_compute in (ss_mem ss_body) in change (ss_mem ss_body) with l in Hrr;
            cbn [In] in Hrr; repeat (destruct Hrr as [Hrr | Hrr]); try (exfalso; exact Hrr); subst rr;
            cbn [YP09.r_wlo YP09.r_whi] in Hbb; lia);
      assert (HM2 : RCS_mem (ms_mem msy)) by (apply (rcs_mem_step (ms_mem ms)); assumption);
      paj_run_to_tok RUNTO HS2 HJ2 SH2 RCS_span RCS_LOOP
    end.
    * cbn [ss_mem]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil.
    * lazymatch goal with
      | HS3 : st_ok_pi _ _ ?Ez ?ssx (restrict _ ?msz), HJ3 : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
        HFr3 : frame_of _ _ (mrestrict _ _) (mrestrict _ _), HG3 : mem_grows _ _ |- _ =>
        assert (Hmm3 : forall x : word, mrestrict (w_H W) (ms_mem msz) x = mrestrict (w_H W) (ms_mem ms) x)
          by (intros xx; rewrite <- Hmm; apply HFr3; intros (rr & Hrr & Hbb);
              cbn [In] in Hrr; repeat (destruct Hrr as [Hrr | Hrr]); try (exfalso; exact Hrr); subst rr;
              cbn [YP09.r_wlo YP09.r_whi] in Hbb; lia);
        assert (HM3 : RCS_mem (ms_mem msz)) by
          (apply (rcs_mem_step (ms_mem ms)); [exact HM | exact Hmm3 | intros xx Hxx; rewrite Hmm3; exact Hxx]);
        assert (HK3 : forall rr : bv 5, In rr RCS_KEEPL -> getr (ms_regs msz) rr = getr regs rr)
          by (apply (regs_kept_of_st_ok_pi Ez ssx (restrict (w_H W) msz) regs ext RCS_KEEPL HS3);
              [eapply env_agree_trans; [exact HAE | split;
                 [intros nn Hnn; rewrite ?ew_ewset_other by lia; reflexivity | reflexivity]]
              | vm_compute; reflexivity]);
        prreg HS3 (2%bv : bv 5) Q2; prreg HS3 (11%bv : bv 5) Q11; prreg HS3 (12%bv : bv 5) Q12;
        prreg HS3 (13%bv : bv 5) Q13; prreg HS3 (14%bv : bv 5) Q14; prreg HS3 (15%bv : bv 5) Q15;
        prreg HS3 (16%bv : bv 5) Q16; prreg HS3 (17%bv : bv 5) Q17;
        rewrite ?ew_ewset_other in Q2, Q11, Q12, Q13, Q14, Q15, Q16, Q17 by lia;
        apply (IH (Datatypes.S i) msz _ ltac:(lia) ltac:(lia) Hn2
                 (st_ok_pi_restrict_mkst (w_H W) Ez ssx msz HS3 eq_refl) HM3 HK3)
      end.
      -- rewrite Q2, E2; unfold w64, spZ; f_equal; lia.
      -- rewrite Q11, E32; unfold w64; rewrite !unsigned_lit_small by lia; f_equal; unfold p; lia.
      -- rewrite Q12, E33, E38; rewrite (alu_add_small (RcModel.psum RS i) bt) by (unfold M64; lia);
         unfold w64; f_equal; rewrite rcs_psum_S; reflexivity.
      -- rewrite Q13, E34; reflexivity.
      -- rewrite Q14, E11, H11; unfold w64; rewrite !unsigned_lit_small by lia; f_equal; lia.
      -- exact Q15.
      -- rewrite Q16, E32; unfold w64; rewrite !unsigned_lit_small by lia; f_equal; unfold p; lia.
      -- rewrite Q17, E35; unfold w64; rewrite !unsigned_lit_small by lia; f_equal; lia.
      -- assumption.
Qed.

(* ---- the entry: the frame, the shadow base, and the n = 1 skip ------------------------------ *)
Definition rcs_eext : list word :=
  rcs_ext 0 0 0 0 (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0).

Lemma rcs_entry_done :
SRr SEGS W (cfg_at SEGS (BASE + AF_reac_ctrl_record_cksum_stamp) regs memc mdc)
  (tb_reac_ctrl_record_cksum_stamp_post B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs r n RS).
Proof.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
pose proof rcs_bounds as (Hr0' & Hrn & Hsp46 & Hspal & Hrau). unfold RCS_HI in Hrn.
pose proof HJ0 as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _ & _).
pose proof HJ0 as HJx.
assert (HEI : img_env VAL A_LIM (RE rcs_eext)) by apply rcs_env.
assert (HAE : env_agree 32 (Ereg regs rcs_eext) (RE rcs_eext)) by apply rcs_agree.
assert (E1 : ew (RE rcs_eext) 1%nat = getr regs 1)
  by (apply (rcs_ew_lo rcs_eext 1%nat 1%bv); [lia | reflexivity]).
assert (E2 : ew (RE rcs_eext) 2%nat = getr regs 2)
  by (apply (rcs_ew_lo rcs_eext 2%nat 2%bv); [lia | reflexivity]).
assert (E10 : ew (RE rcs_eext) 10%nat = getr regs 10)
  by (apply (rcs_ew_lo rcs_eext 10%nat 10%bv); [lia | reflexivity]).
assert (E11 : ew (RE rcs_eext) 11%nat = getr regs 11)
  by (apply (rcs_ew_lo rcs_eext 11%nat 11%bv); [lia | reflexivity]).
assert (E34 : ew (RE rcs_eext) 34%nat = Z_to_bv 64 SHADOW_OFF)
  by (rewrite (rcs_ew_hi rcs_eext 34%nat 2%nat eq_refl ltac:(lia)); reflexivity).
assert (Usp : bv_unsigned (ew (RE rcs_eext) 2%nat) = spZ regs) by (rewrite E2; reflexivity).
assert (Hsb : nth 2 rcs_eext (Z_to_bv 64 0) = Z_to_bv 64 SHADOW_OFF) by reflexivity.
unfold cfg_at. change (w64 (BASE + AF_reac_ctrl_record_cksum_stamp))
  with (Z_to_bv 64 (BASE + AF_reac_ctrl_record_cksum_stamp)).
destruct (Z.eq_dec n 1) as [Hn1e | Hn1n].
- (* n = 1: the loop is skipped and the stamp is 0 *)
  assert (HRS : RS = []) by (destruct RS as [|x l]; [reflexivity | cbn [length] in Hlen; lia]).
  assert (HS : st_ok_pi SEGS VAL (RE rcs_eext) ss_ent1
                 (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + RCS_ENT)) memc (seg_rom SEGS)))).
  { unfold ss_ent1. apply (rcs_ent_ok rcs_eregs1 1 1 rcs_eext Hsb); [|lia].
    rewrite rcs_eregs1_eq. apply regs_ok_rereg; [apply regs_ok_Eimg_Ereg | reflexivity|].
    rewrite H11, Hn1e. reflexivity. }
  assert (SHOK : sh_ok SEGS RCS_Bx [] (RE rcs_eext) (mrestrict (w_H W) memc)) by constructor.
  paj_run_to_tok RUNTO HS HJx SHOK RCS_span RCS_TAIL.
  + unfold ss_ent1. cbn [ss_mem]. unfold rcs_stk0.
    eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (spZ regs - sp0));
    [reflexivity | cbn [YP09.r_base]; rewrite Usp; lia | cbn [YP09.r_wlo]; unfold RCS_STK in Hwlo; lia
    | cbn [YP09.r_whi]; lia |].
    apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil.
  + lazymatch goal with
    | HS2 : st_ok_pi _ _ ?Ez ?ssx (restrict _ ?msy), HJ2 : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
      HFr2 : frame_of _ _ (mrestrict _ _) (mrestrict _ _), HG2 : mem_grows _ _ |- _ =>
      assert (Hmm : forall x : word, ~ (spZ regs - 16 <= bv_unsigned x < spZ regs) ->
                mrestrict (w_H W) (ms_mem msy) x = mrestrict (w_H W) memc x)
        by (intros xx Hxx; apply HFr2; intros (rr & Hrr & Hbb);
            let l := eval vm_compute in (ss_mem ss_ent1) in change (ss_mem ss_ent1) with l in Hrr;
            cbn [In] in Hrr; repeat (destruct Hrr as [Hrr | Hrr]); try (exfalso; exact Hrr); subst rr;
            cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val] in Hbb;
            rewrite ?ew_ewset_other in Hbb by lia; rewrite ?Usp in Hbb; lia);
      pose proof (st_ok_mem_ok SEGS Ez (abs_ss VAL ssx) (restrict (w_H W) msy) HS2) as HMO;
      cbn [abs_ss setpc ss_mem restrict ms_mem] in HMO;
      destruct HMO as (_ & HMO & _);
      let l := eval vm_compute in (ss_mem ssx) in change (ss_mem ssx) with l in HMO;
      apply Forall_inv in HMO; destruct HMO as (_ & _ & _ & HCH);
      cbn [YP09.r_base] in HCH;
      assert (Hb2 : base_val Ez (Some 2%nat) = spZ regs)
        by (cbn [base_val]; rewrite ?ew_ewset_other by lia; exact Usp);
      rewrite Hb2 in HCH;
      pose proof (Forall_inv HCH) as Hcra; cbn [YP09.c_off YP09.c_val] in Hcra;
      pose proof (val_of_chunk_ok SEGS Ez (mrestrict (w_H W) (ms_mem msy)) (spZ regs) (-8) 8
        (SOff 1%nat 0) (raZ regs) Hcra
        ltac:(cbn [sv_denot]; rewrite ?ew_ewset_other by lia; rewrite E1, Z.add_0_r;
              unfold raZ; rewrite Z_to_bv_bv_unsigned; reflexivity)
        ltac:(cbn; lia) ltac:(cbn; lia)) as Hval8;
      cbn [N.to_nat] in Hval8;
      assert (HM2 : RCS_mem (ms_mem msy))
        by (split; [exact Hmm | split;
              [exact HG2 | replace (spZ regs - 8) with (spZ regs + -8) by lia; exact Hval8]]);
      assert (HK2 : forall rr : bv 5, In rr RCS_KEEPL -> getr (ms_regs msy) rr = getr regs rr)
        by (apply (regs_kept_of_st_ok_pi Ez ssx (restrict (w_H W) msy) regs rcs_eext RCS_KEEPL HS2);
            [eapply env_agree_trans; [exact HAE | split;
               [intros nn Hnn; rewrite ?ew_ewset_other by lia; reflexivity | reflexivity]]
            | vm_compute; reflexivity]);
      prreg HS2 (2%bv : bv 5) Q2; prreg HS2 (11%bv : bv 5) Q11; prreg HS2 (12%bv : bv 5) Q12;
      prreg HS2 (13%bv : bv 5) Q13;
      rewrite ?ew_ewset_other in Q2, Q11, Q12, Q13 by lia;
      apply (rcs_tail_done msy _ (r + n - 1) (RcModel.psum RS (length RS))
               (getr (ms_regs msy) 5) (getr (ms_regs msy) 6) (getr (ms_regs msy) 14)
               (getr (ms_regs msy) 15) (getr (ms_regs msy) 16) (getr (ms_regs msy) 17));
      [ exact (st_ok_pi_restrict_mkst (w_H W) Ez ssx msy HS2 eq_refl)
      | exact HM2 | exact HK2
      | rewrite Q2, E2; unfold w64, spZ; f_equal; lia
      | reflexivity | reflexivity
      | rewrite Q11, E10, H10; unfold w64; f_equal; lia
      | rewrite Q12; unfold w64; f_equal; rewrite HRS; cbn [length RcModel.psum]; reflexivity
      | rewrite Q13, E34; reflexivity
      | reflexivity | reflexivity | reflexivity | reflexivity
      | reflexivity | reflexivity | exact HJ2 ]
    end.
- (* 2 <= n: the loop runs n - 1 times *)
  assert (Hn2 : 2 <= n) by lia.
  assert (HS : st_ok_pi SEGS VAL (RE rcs_eext) ss_ent
                 (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + RCS_ENT)) memc (seg_rom SEGS)))).
  { unfold ss_ent. apply (rcs_ent_ok rcs_eregs 2 RCS_HI rcs_eext Hsb); [|unfold RCS_HI; lia].
    rewrite rcs_eregs_eq. apply regs_ok_Eimg_Ereg. }
  assert (SHOK : sh_ok SEGS RCS_Bx [] (RE rcs_eext) (mrestrict (w_H W) memc)) by constructor.
  paj_run_to_tok RUNTO HS HJx SHOK RCS_span RCS_LOOP.
  + unfold ss_ent. cbn [ss_mem]. unfold rcs_stk0.
    eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (spZ regs - sp0));
    [reflexivity | cbn [YP09.r_base]; rewrite Usp; lia | cbn [YP09.r_wlo]; unfold RCS_STK in Hwlo; lia
    | cbn [YP09.r_whi]; lia |].
    apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil.
  + lazymatch goal with
    | HS2 : st_ok_pi _ _ ?Ez ?ssx (restrict _ ?msy), HJ2 : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
      HFr2 : frame_of _ _ (mrestrict _ _) (mrestrict _ _), HG2 : mem_grows _ _ |- _ =>
      assert (Hmm : forall x : word, ~ (spZ regs - 16 <= bv_unsigned x < spZ regs) ->
                mrestrict (w_H W) (ms_mem msy) x = mrestrict (w_H W) memc x)
        by (intros xx Hxx; apply HFr2; intros (rr & Hrr & Hbb);
            let l := eval vm_compute in (ss_mem ss_ent) in change (ss_mem ss_ent) with l in Hrr;
            cbn [In] in Hrr; repeat (destruct Hrr as [Hrr | Hrr]); try (exfalso; exact Hrr); subst rr;
            cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val] in Hbb;
            rewrite ?ew_ewset_other in Hbb by lia; rewrite ?Usp in Hbb; lia);
      pose proof (st_ok_mem_ok SEGS Ez (abs_ss VAL ssx) (restrict (w_H W) msy) HS2) as HMO;
      cbn [abs_ss setpc ss_mem restrict ms_mem] in HMO;
      destruct HMO as (_ & HMO & _);
      let l := eval vm_compute in (ss_mem ssx) in change (ss_mem ssx) with l in HMO;
      apply Forall_inv in HMO; destruct HMO as (_ & _ & _ & HCH);
      cbn [YP09.r_base] in HCH;
      assert (Hb2 : base_val Ez (Some 2%nat) = spZ regs)
        by (cbn [base_val]; rewrite ?ew_ewset_other by lia; exact Usp);
      rewrite Hb2 in HCH;
      pose proof (Forall_inv HCH) as Hcra; cbn [YP09.c_off YP09.c_val] in Hcra;
      pose proof (val_of_chunk_ok SEGS Ez (mrestrict (w_H W) (ms_mem msy)) (spZ regs) (-8) 8
        (SOff 1%nat 0) (raZ regs) Hcra
        ltac:(cbn [sv_denot]; rewrite ?ew_ewset_other by lia; rewrite E1, Z.add_0_r;
              unfold raZ; rewrite Z_to_bv_bv_unsigned; reflexivity)
        ltac:(cbn; lia) ltac:(cbn; lia)) as Hval8;
      cbn [N.to_nat] in Hval8;
      assert (HM2 : RCS_mem (ms_mem msy))
        by (split; [exact Hmm | split;
              [exact HG2 | replace (spZ regs - 8) with (spZ regs + -8) by lia; exact Hval8]]);
      assert (HK2 : forall rr : bv 5, In rr RCS_KEEPL -> getr (ms_regs msy) rr = getr regs rr)
        by (apply (regs_kept_of_st_ok_pi Ez ssx (restrict (w_H W) msy) regs rcs_eext RCS_KEEPL HS2);
            [eapply env_agree_trans; [exact HAE | split;
               [intros nn Hnn; rewrite ?ew_ewset_other by lia; reflexivity | reflexivity]]
            | vm_compute; reflexivity]);
      prreg HS2 (2%bv : bv 5) Q2; prreg HS2 (11%bv : bv 5) Q11; prreg HS2 (12%bv : bv 5) Q12;
      prreg HS2 (13%bv : bv 5) Q13; prreg HS2 (14%bv : bv 5) Q14; prreg HS2 (15%bv : bv 5) Q15;
      prreg HS2 (16%bv : bv 5) Q16; prreg HS2 (17%bv : bv 5) Q17;
      rewrite ?ew_ewset_other in Q2, Q11, Q12, Q13, Q14, Q15, Q16, Q17 by lia;
      apply (rcs_loop (length RS) 0 msy _ ltac:(lia) ltac:(lia) Hn2
               (st_ok_pi_restrict_mkst (w_H W) Ez ssx msy HS2 eq_refl) HM2 HK2)
    end.
    * rewrite Q2, E2; unfold w64, spZ; f_equal; lia.
    * rewrite Q11, E10, H10; unfold w64; f_equal; lia.
    * rewrite Q12; unfold w64; f_equal; cbn [RcModel.psum]; reflexivity.
    * rewrite Q13, E34; reflexivity.
    * rewrite Q14, E11, H11; unfold w64; rewrite !unsigned_lit_small by lia; f_equal; lia.
    * exact Q15.
    * rewrite Q16, E10, H10; unfold w64; f_equal; lia.
    * rewrite Q17, E11, H11; unfold w64; rewrite !unsigned_lit_small by lia; f_equal; lia.
    * assumption.
Qed.

End C.
End H.

(* The walk: the contract of lib/B/Prog/GrantBContracts.v:835-836, from the runtime laws and PALib. *)
Theorem pb_reac_ctrl_record_cksum_stamp : walk_reac_ctrl_record_cksum_stamp B.
Proof.
unfold walk_reac_ctrl_record_cksum_stamp, hyps_reac_ctrl_record_cksum_stamp, RT_LAWS, RT_PALIB.
intros [HL HP]. unfold tb_reac_ctrl_record_cksum_stamp_spec.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs r n RS
  HJ Hra Hra4 Hgp Htp H10 H11 Hal16 Hwlo Hwhi Hn1 Hlen HGB Hr0 Hamem Himg Hpsp HWR HRA.
apply (rcs_entry_done HL HP STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs r n RS);
assumption.
Qed.
End W.
