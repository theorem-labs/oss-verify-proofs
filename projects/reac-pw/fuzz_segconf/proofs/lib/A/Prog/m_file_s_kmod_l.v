(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the loop segment of answer's ASan walk (plugin-hostd/fuzz_command, 0x8a4c0):
   syntax_instantiate's loop from its head HEAD (0x8a670) to JOIN (0x8a734), an_head_ok : AN_JOIN_stmt ->
   AN_HEAD_stmt (lib/A/Prog/answer_s1.v), by strong induction on the bytes of the shape left, in the form of
   proofs/cgif/cgif_file_fuzzer/lib/A/AC8b.v (tcbb_loopX, a loop with inline checks, re-seeded at each iteration). The
   plain proof of the same loop is lib/Prog/answer.v:120-226 (an_loop). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/answer_l.v, with its module paths, module names and numbers changed; 344 of its 463 lines of code are new or changed and 668 lines of the source are left out. *)
(* m_file on fuzz_segconf.asan (image A): the fold loop of segment S_MF_KMOD, MK_FOLD 0x867f8 .. 0x86848, in the
   form of plugin-hostd/fuzz_command's lib/A/Prog/answer_l.v (a loop with inline checks, re-seeded at each pass).
   The KMOD fold sub-lane of the G2 walk owner's G2. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YP0j YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0n YI0s YI16 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05 YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList SegAddr SegPa.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPaLib PaLibG PaLibH PaSB PaDenot PaLibF PaCall PaCallRun.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegObj SegGlob SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import m_file_c m_file_m m_file_s_kmod_m m_file_s_kmod_t m_file_k.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require SegInstA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the symbolic state at MK_FOLD, one pass's seed ----
   Every register is its own atom except a2 = a1 (pinned to atom 11) and s5 = a0 (pinned to atom 10). Atom 10 is the
   value cursor A = p + ov + i, 11 the low cursor P = FB + 32 + i, 18 = s2 the shadow base; the extra atom 32 is the
   value byte at A. The regions are the value byte (read only) and low's byte at P (written). The one shadow entry
   covers low's byte at P, so the store's inline check needs nothing; the load's check leaves the obligation that A
   is addressable. *)
Definition mkl_regs : list sv := sr_set (sr_set sr_atoms 12%bv (SOff 11 0)) 21%bv (SOff 10 0).
Definition mkl_regions : smem :=
[ YP09.mkRegion (Some 10%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 32 0))];
  YP09.mkRegion (Some 11%nat) 0 1 0 1 [] ].
Definition mkl_facts : facts :=
mkFacts [ (10%nat, PTR 0); (11%nat, PTR 0); (32%nat, mkAF 0 255 0); (18%nat, mkAF SB SB 0) ] [] [].
Definition mkl_ss : sstate := mkSS MK_FOLD mkl_regs mkl_regions None mkl_facts.
Definition mkl_Bx : sv := SOff 18 0.
Definition mkl_SH : list shent := [mkSHE 11 0 1].
(* the registers a pass does not touch *)
Definition MKL_KEPT : list (bv 5) := [2; 3; 4; 8; 9; 18; 19; 20; 22; 23; 24; 25; 26; 27]%bv.
(* the byte a pass stores, low[i] = v[i] + ((v[i] - 65) <u 26) << 5 (0x8681c .. 0x86834) *)
Definition mkl_wv : sv := SAlu ALU_ADD (SOff 32 0) (SAlu ALU_SLL (SAlu ALU_SLTU (SOff 32 (-65)) (SLit 26)) (SLit 5)).

(* ---- lists and the fold (pure) ---- *)
Lemma mkl_line_len : forall rest, (length (mf_line rest) <= length rest)%nat.
Proof.
unfold mf_line. induction rest as [|b r IH]; [cbn; lia|]. cbn [break_nl].
destruct (b =? NL); [cbn; lia|]. destruct (break_nl r) as [l q]. cbn [fst length] in *. lia.
Qed.
Lemma mkl_nth_skipn : forall (l : list Z) o k, nth k (skipn o l) 0 = nth (o + k) l 0.
Proof.
intros l o. revert l. induction o as [|o IH]; intros l k; [reflexivity|].
destruct l as [|x l]; [destruct k; reflexivity|]. cbn [skipn]. rewrite IH. reflexivity.
Qed.
Lemma mkl_nth_firstn : forall (l : list Z) n k, (k < n)%nat -> nth k (firstn n l) 0 = nth k l 0.
Proof.
induction l as [|x l IH]; intros n k Hk; destruct n as [|n]; try lia; [destruct k; reflexivity|].
destruct k as [|k]; [reflexivity|]. cbn [firstn nth]. apply IH. lia.
Qed.
(* the stored byte is lower(v[i]): checked over the 256 byte values *)
Definition mkl_fz (c : Z) : Z :=
zcanon (c + zcanon (Z.shiftl (zcanon (if zcanon (c + -65) <? 26 then 1 else 0)) (Z.land 5 63))) mod 256.
Lemma mkl_fz_lower : forall c, 0 <= c < 256 -> mkl_fz c = lower c.
Proof.
assert (Hall : forallb (fun k => mkl_fz (Z.of_nat k) =? lower (Z.of_nat k)) (seq 0 256) = true)
  by (vm_compute; reflexivity).
intros c Hc. rewrite forallb_forall in Hall. specialize (Hall (Z.to_nat c)). rewrite Z2Nat.id in Hall by lia.
apply Z.eqb_eq, Hall, in_seq. lia.
Qed.
(* low[0 .. i] after a pass: low[0 .. i) kept, low[i] written *)
Lemma mkl_zs_ext : forall (rd rd' : reader) F vv i Pz,
(i < length vv)%nat -> Pz = F + 32 + Z.of_nat i -> 0 <= F -> F + 32 + Z.of_nat i < 2 ^ 64 ->
sa_zs rd (F + 32) (map lower (firstn i vv)) ->
(forall a, 0 <= a < 2 ^ 64 -> a <> Pz -> rd' a = rd a) ->
rd' Pz = Some (lower (nth i vv 0)) ->
sa_zs rd' (F + 32) (map lower (firstn (S i) vv)).
Proof.
intros rd rd' F vv i Pz Hi HP HF HF64 HZ KM HW.
rewrite (map_lower_firstn_S vv i Hi).
intros k Hk. rewrite length_app, length_map, length_firstn in Hk. cbn [length] in Hk.
destruct (Nat.eq_dec k i) as [->|Hne].
- rewrite app_nth2 by (rewrite length_map, length_firstn; lia). rewrite length_map, length_firstn.
  replace (i - Nat.min i (length vv))%nat with 0%nat by lia. cbn [nth]. rewrite <- HP. exact HW.
- rewrite app_nth1 by (rewrite length_map, length_firstn; lia). rewrite KM by lia. apply HZ.
  rewrite length_map, length_firstn. lia.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ seg_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

Definition mkl_E (regs1 : bvmap 5 word) (Cz : Z) : env := Eimg (Ereg regs1 [Z_to_bv 64 Cz]).

Lemma mkl_ew_reg : forall regs1 Cz n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (mkl_E regs1 Cz) n = getr regs1 r.
Proof.
intros regs1 Cz n r Hn. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
unfold mkl_E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn.
Qed.
Lemma mkl_ew32 : forall regs1 Cz, ew (mkl_E regs1 Cz) 32 = Z_to_bv 64 Cz.
Proof. intros. unfold mkl_E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs1 _ 0). Qed.
Lemma mkl_env_agree : forall regs1 Cz, env_agree 32 (Ereg regs1 [Z_to_bv 64 Cz]) (mkl_E regs1 Cz).
Proof. intros. split; [intros n Hn; unfold mkl_E; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity | reflexivity]. Qed.

Section e.
Variable B : asyms.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

(* the seed of a pass *)
Lemma mkl_entry : forall (W : world SEGS) (regs1 : bvmap 5 word) memc A P Cz,
getr regs1 10 = w64 A -> getr regs1 21 = w64 A -> getr regs1 11 = w64 P -> getr regs1 12 = w64 P ->
getr regs1 18 = w64 SB ->
4096 <= A <= 140737479966720 -> 4096 <= P <= 140737479966720 -> 0 <= Cz <= 255 ->
rdW W memc A = Some Cz -> apresent (w_H W) memc P -> (A + 1 <= P \/ P + 1 <= A) ->
st_ok_pi SEGS VAL (mkl_E regs1 Cz) mkl_ss
  (restrict (w_H W) (mkst regs1 (Z_to_bv 64 (BASE + MK_FOLD)) memc (seg_rom SEGS))).
Proof.
intros W regs1 memc A P Cz H10 H21 H11 H12 H18 HA HP HC HrdA HpP Hdisj.
set (E := mkl_E regs1 Cz).
assert (E10 : ew E 10 = Z_to_bv 64 A) by (subst E; rewrite (mkl_ew_reg regs1 Cz 10 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 P) by (subst E; rewrite (mkl_ew_reg regs1 Cz 11 11%bv eq_refl); exact H11).
assert (E18 : ew E 18 = Z_to_bv 64 SB) by (subst E; rewrite (mkl_ew_reg regs1 Cz 18 18%bv eq_refl); exact H18).
assert (E32 : ew E 32 = Z_to_bv 64 Cz) by (subst E; apply mkl_ew32).
rewrite restrict_mkst_fx. unfold mkl_ss. apply pa_entry_st_ok_full.
- unfold mkl_regs. apply regs_ok_pin;
    [apply regs_ok_pin; [apply regs_ok_Eimg_Ereg | intros X; discriminate X | idtac] | intros X; discriminate X | idtac].
  + cbn [sv_denot]. rewrite E11, unsigned_lit_small, Z.add_0_r by lia. exact H12.
  + cbn [sv_denot]. rewrite E10, unsigned_lit_small, Z.add_0_r by lia. exact H21.
- vm_compute. reflexivity.
- constructor; [|constructor; [|constructor]].
  + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E10, unsigned_lit_small by lia.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
    unfold YP09.chunk_ok, YP09.c_len, YP09.cv_len. cbn [YP09.c_off YP09.c_val]. intros i Hi. assert (i = 0) as -> by lia.
    destruct (aview_byte SEGS (w_H W) memc A Cz HrdA) as (b & Hb & Hv & _).
    exists b. split.
    * cbn [YP09.cbyte]. f_equal. unfold YP09.byte_of_word. cbn [sv_denot]. rewrite E32.
      rewrite !Z.add_0_r, (unsigned_lit_small Cz), (unsigned_lit_small Cz) by lia. change (8 * 0) with 0. rewrite Z.shiftr_0_r.
      subst Cz. apply Z_to_bv_bv_unsigned.
    * rewrite !Z.add_0_r. exact Hb.
  + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E11, unsigned_lit_small by lia.
    split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. assert (o = 0) as -> by lia. rewrite Z.add_0_r. apply (apresent_writable SEGS). exact HpP.
- unfold mkl_regions. cbn [YP09.pairwise_disjoint YP09.all_disjoint]. unfold YP09.extent_disjoint.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.base_val].
  rewrite E10, E11, !unsigned_lit_small by lia. repeat split; lia.
- split; [|split; [exact I | exact I]].
  cbn [mkl_facts f_atoms atoms_ok]. unfold afact_ok, PTR. cbn [af_lo af_hi af_al2].
  rewrite E10, E11, E32, E18, !unsigned_lit_small by (unfold SB; lia).
  rewrite Z.pow_0_r, !Z.mod_1_r. unfold SB. repeat split; lia.
Qed.

(* the shadow entry: low's byte at P is addressable and is not a shadow byte *)
Lemma mkl_shok : forall (W : world SEGS) (regs1 : bvmap 5 word) memc P Cz,
getr regs1 18 = w64 SB -> getr regs1 11 = w64 P -> 4096 <= P < 2 ^ 47 ->
range_addressable (rdW W memc) SHADOW_OFF P 1 -> ~ (SB <= P < SB + 17592186044416) ->
sh_ok SEGS mkl_Bx mkl_SH (mkl_E regs1 Cz) (mrestrict (w_H W) memc).
Proof.
intros W regs1 memc P Cz H18 H11 HP Hra Hap.
assert (E18 : ew (mkl_E regs1 Cz) 18 = Z_to_bv 64 SB) by (rewrite (mkl_ew_reg regs1 Cz 18 18%bv eq_refl); exact H18).
assert (E11 : ew (mkl_E regs1 Cz) 11 = Z_to_bv 64 P) by (rewrite (mkl_ew_reg regs1 Cz 11 11%bv eq_refl); exact H11).
assert (UB : U (mkl_E regs1 Cz) mkl_Bx = SB) by (unfold mkl_Bx; apply (U_atom _ 18 SB E18); unfold SB; lia).
assert (UP : U (mkl_E regs1 Cz) (SOff 11 0) = P) by (apply (U_atom _ 11 P E11); lia).
constructor; [|constructor]. split.
- cbn [she_m she_lo she_hi]. rewrite UB, UP, Z.add_0_r. change (1 - 0) with 1. rewrite SB_SHADOW_OFF. exact Hra.
- intros a. cbn [she_m she_lo she_hi]. rewrite UB, UP. change (Z.min 0 1) with 0. change (Z.max 0 1) with 1. lia.
Qed.

(* the write of a pass: low's byte at P, in m_file's own side-stack frame (class 1) *)
Lemma mkl_awr : forall E cs0 cs1 STK sp0 FP bl0 blc fr0 lyc pos,
frame_addr lyc 1 pos <= bv_unsigned (ew E 11) < frame_addr lyc 1 pos + fs_frame_bytes 1 ->
awr_ok SEGS B E [YP09.mkRegion (Some 10%nat) 0 1 0 0 cs0; YP09.mkRegion (Some 11%nat) 0 1 0 1 cs1]
STK sp0 FP bl0 blc fr0 lyc [(1, pos)].
Proof.
intros E cs0 cs1 STK sp0 FP bl0 blc fr0 lyc pos HP.
apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|].
eapply (YCbq.awr_ok_cons_gen SEGS B _ _ _ _ _ _ _ _ _ _ _ 11%nat (bv_unsigned (ew E 11)));
  [reflexivity | reflexivity | | apply awr_ok_nil].
cbn [YP09.r_wlo YP09.r_whi]. intros a Ha. right. right. right. left.
exists 1, pos. split; [left; reflexivity|]. left. unfold in_zr. cbn [fst snd]. lia.
Qed.

(* ---- the facts the symbolic runs of a pass leave ---- *)
(* a run writes at most low's byte at P (the windows of the two regions) *)
Lemma mkl_keep_step : forall E cs0 cs1 (m0 m m' : word -> option byte) (H : word -> bool) Pz,
frame_of E [YP09.mkRegion (Some 10%nat) 0 1 0 0 cs0; YP09.mkRegion (Some 11%nat) 0 1 0 1 cs1] (mrestrict H m) (mrestrict H m') ->
bv_unsigned (ew E 11) = Pz ->
(forall a, 0 <= a < 2 ^ 64 -> a <> Pz -> aview SEGS H m a = aview SEGS H m0 a) ->
forall a, 0 <= a < 2 ^ 64 -> a <> Pz -> aview SEGS H m' a = aview SEGS H m0 a.
Proof.
intros E cs0 cs1 m0 m m' H Pz HFr H11 KM a Ha Hn.
assert (HW : forall b wlo whi a', In (b, wlo, whi) (windows [YP09.mkRegion (Some 10%nat) 0 1 0 0 cs0; YP09.mkRegion (Some 11%nat) 0 1 0 1 cs1]) ->
  base_val E b + wlo <= a' < base_val E b + whi -> a' = Pz).
{ intros b wlo whi a' Hin Hr. cbn [windows map YP09.r_base YP09.r_wlo YP09.r_whi In] in Hin.
  destruct Hin as [Hq | [Hq | []]]; injection Hq as <- <- <-; cbn [base_val] in Hr; lia. }
rewrite (kept_of_frame (segs := SEGS) E _ H m m' (fun a' => a' = Pz) HFr HW a Ha Hn). exact (KM a Ha Hn).
Qed.
(* the byte a run wrote at P *)
Lemma mkl_wbyte : forall E ss ms (H : word -> bool) Pz v,
st_ok_pi SEGS VAL E ss (restrict H ms) ->
nth_error (ss_mem ss) 1 = Some (YP09.mkRegion (Some 11%nat) 0 1 0 1 [YP09.mkChunk 0 (CVal 1 v)]) ->
bv_unsigned (ew E 11) = Pz ->
aview SEGS H (ms_mem ms) Pz = Some (bv_unsigned (sv_denot E v) mod 256).
Proof.
intros E ss ms H Pz v HS Hn H11.
pose proof (st_ok_pi_region_nth E ss (restrict H ms) 1 _ HS Hn) as Hr.
pose proof (field_of_region_any E _ 11 Pz _ 0 1 0 1 0 1%N v Hr H11 (or_introl eq_refl) ltac:(lia)) as V.
cbn [ms_mem restrict] in V. rewrite Z.add_0_r in V. change (2 ^ (8 * Z.of_N 1)) with 256 in V.
apply aview_of_val_mem1; [exact V | apply Z.mod_pos_bound; lia].
Qed.
(* the stored byte is lower(v[i]) *)
Lemma mkl_store : forall E c, ew E 32 = Z_to_bv 64 c -> 0 <= c < 256 ->
bv_unsigned (sv_denot E mkl_wv) mod 256 = lower c.
Proof.
intros E c H Hc. rewrite <- (mkl_fz_lower c Hc). unfold mkl_fz, mkl_wv.
change (bv_unsigned (sv_denot E (SAlu ALU_ADD (SOff 32 0)
  (SAlu ALU_SLL (SAlu ALU_SLTU (SOff 32 (-65)) (SLit 26)) (SLit 5)))))
  with (U E (SAlu ALU_ADD (SOff 32 0) (SAlu ALU_SLL (SAlu ALU_SLTU (SOff 32 (-65)) (SLit 26)) (SLit 5)))).
rewrite !U_SAlu. rewrite (U_atom E 32 c H) by lia. rewrite U_SOff, H, unsigned_lit_small by lia.
rewrite !U_lit by lia. cbn [zalu_raw]. reflexivity.
Qed.
Lemma mkl_ag32 : forall (regs1 : bvmap 5 word) extra E0 E,
env_agree 32 (Ereg regs1 extra) E0 -> env_agree 33 E0 E -> env_agree 32 (Ereg regs1 extra) E.
Proof. intros regs1 extra E0 E H0 H1. eapply env_agree_trans; [exact H0 | eapply env_agree_le; [|exact H1]; lia]. Qed.
Lemma mkl_ag_ew : forall E0 E n v, env_agree 33 E0 E -> (n < 33)%nat -> ew E0 n = Z_to_bv 64 v -> ew E n = Z_to_bv 64 v.
Proof. intros E0 E n v H Hn H0. rewrite (proj1 H n Hn). exact H0. Qed.
Lemma mkl_u11 : forall E0 E P, env_agree 33 E0 E -> ew E0 11 = Z_to_bv 64 P -> 0 <= P < 2 ^ 64 -> bv_unsigned (ew E 11) = P.
Proof. intros E0 E P H H0 HP. rewrite (proj1 H 11%nat ltac:(lia)), H0. apply unsigned_lit_small. exact HP. Qed.
(* the back edge `bnez a3` 0x86844, a3 = (ln - i) - 1 *)
Lemma mkl_br : forall E v b, ew E 13 = Z_to_bv 64 v -> 1 <= v < 2 ^ 63 ->
branch_taken BC_NE (sv_denot E (SOff 13 (-1))) (sv_denot E (SLit 0)) = b -> negb (v + -1 =? 0) = b.
Proof.
intros E v b H Hv Hc. rewrite branch_ne_U, (U_atom_off E 13 v (-1) H) in Hc by lia. rewrite U_lit in Hc by lia.
exact Hc.
Qed.

(* ---- what a pass knows from mk_base: the frame, low's shadow, the text, the value ---- *)
Lemma mkl_base_facts : forall n v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest ov vl vv,
mk_base B n v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest ov vl vv ->
4096 <= frame_addr lyc 1 pos /\ frame_addr lyc 1 pos + 128 <= alloc_ceiling /\
in_app (frame_addr lyc 1 pos) 128 /\
(forall a, frame_addr lyc 1 pos <= a < frame_addr lyc 1 pos + 128 -> apresent (w_H Wc) memc a) /\
range_addressable (rdW Wc memc) SHADOW_OFF (frame_addr lyc 1 pos + 32) 64 /\
(forall k, (k <= length rest)%nat -> 4096 <= p + Z.of_nat k /\ p + Z.of_nat k < alloc_ceiling /\
  ~ (frame_addr lyc 1 pos <= p + Z.of_nat k < frame_addr lyc 1 pos + 128)) /\
sa_str (rdW Wc memc) p rest /\ range_addressable (rdW Wc memc) SHADOW_OFF p (Z.of_nat (length rest) + 1) /\
length vv = vl /\ (ov + vl <= length rest)%nat /\ getr regs1 18 = w64 SHADOW_OFF.
Proof.
intros n v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest ov vl vv HB.
destruct HB as (HCX & HLS & HFRM & HCORE & HCELLS & HREGS & Hn & Hne & HLOOP & Hovl & Hvv & HNP & H24 & H22).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct HCORE as (HJ & Hperm & Hflag & Hlow & _).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfr & _).
assert (Hin : In (1, pos) (frames Sc)) by (rewrite Hfr; left; reflexivity).
assert (FB : fs_frame_bytes 1 = 128) by reflexivity.
destruct (frames_bounds SEGS B LAWS lyc Sc Wc memc mdc 1 pos HAR Hin) as (Hf1 & Hf2 & Hf3). rewrite FB in Hf2, Hf3.
destruct (al_frames _ _ LAWS lyc Sc Wc memc mdc 1 pos HAR Hin) as (Hf32 & _ & Hfp & _). rewrite FB in Hfp.
destruct HCX as (HPRE & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HMP & _).
destruct HMP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HsL & HtH & _).
destruct HtH as (bt & mt & Hbt & Hbt1 & Hbt2).
destruct HLOOP as (Hrl & Hrs & Hp & Hstr & Haddr & _).
assert (Hbt' : In (bt, mt) (ablocks B lyc Sc)) by (apply (Permutation_in _ (Permutation_sym Hperm)); exact Hbt).
destruct (al_blocks _ _ LAWS lyc Sc Wc memc mdc bt mt HAR Hbt') as (_ & Hb4096 & Hbceil & _ & _ & _ & Hm).
pose proof (req_size_pos mt ltac:(lia)) as [_ Hrk].
pose proof (sep_block_frame SEGS B LAWS lyc Sc Wc memc mdc bt mt 1 pos HAR Hbt' Hin) as Hsep.
unfold zdisjoint in Hsep. cbn [fst snd] in Hsep. rewrite FB in Hsep.
pose proof (mkl_line_len rest) as HLL.
set (F := frame_addr lyc 1 pos) in *.
split; [lia|]. split; [lia|]. split; [exact Hf3|]. split; [intros a Ha; exact (proj1 (Hfp a Ha))|].
split.
{ assert (F8 : (F + 32) mod 8 = 0).
  { pose proof (Z.div_mod F 32 ltac:(lia)) as DF. rewrite Hf32 in DF.
    replace (F + 32) with ((4 * (F / 32) + 4) * 8) by lia. apply Z_mod_mult. }
  apply (zero_shadow_range _ _ (F + 32) 64 F8 eq_refl).
  intros j Hj. change (64 / 8) with 8 in Hj. unfold shadow_of_addr.
  replace (SHADOW_OFF + (F + 32) / 8 + j) with (SHADOW_OFF + F / 8 + (4 + j)).
  2:{ replace (F + 32) with (F + 4 * 8) by lia. rewrite Z.div_add by lia. lia. }
  apply (aview_of_val_mem1 SEGS (w_H Wc) memc); [exact (Hlow (4 + j) ltac:(lia)) | unfold MF_LOW_ON; lia]. }
split.
{ intros k Hk. rewrite Hp. split; [lia|]. split; [lia|]. lia. }
split; [exact Hstr|]. split; [destruct Haddr as (_ & _ & _ & HRA & _); exact HRA|].
split; [rewrite <- Hvv, length_firstn, length_skipn; lia|]. split; [lia|].
destruct HREGS as (_ & _ & _ & _ & _ & H18 & _). exact H18.
Qed.

(* what a pass keeps: mk_base after a run that wrote only low's byte at Pz and kept the registers MKL_KEPT; from the
   run-keep kit (m_file_k.v: mf_tx_core / mf_tx_cells / mf_tx_np / mf_tx_loop over mf_win, which covers low.i,
   and mf_regs_at_of) *)
Definition MKL_KEEP : Prop :=
forall n v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest ov vl vv regs1' memc' mdc' Pz,
mk_base B n v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest ov vl vv ->
ajournal SEGS B SegInstA.STK_m_file (mv_sp v) (M_FILE_FP (mv_c v) (mv_k0 v) (mf_final v)) (mv_ly v) (mv_S v)
  (mv_W v) (mv_mem v) (mv_md v) [(1, pos)] lyc Sc Wc memc' mdc' 0 ->
frame_addr lyc 1 pos + 32 <= Pz < frame_addr lyc 1 pos + 96 ->
(forall a, 0 <= a < 2 ^ 64 -> a <> Pz -> rdW Wc memc' a = rdW Wc memc a) ->
(exists z, rdW Wc memc' Pz = Some z) ->
(forall r, In r MKL_KEPT -> getr regs1' r = getr regs1 r) ->
mk_base B n v lyc Sc Wc regs1' memc' mdc' pos mcc gi line p rest ov vl vv.

(* a byte address is taken mod 2^64 *)
Lemma mkl_aview_mod : forall (H : word -> bool) (m : word -> option byte) a,
aview SEGS H m a = aview SEGS H m (a mod 2 ^ 64).
Proof.
intros H m a. unfold aview, mbyte. replace (Z_to_bv 64 (a mod 2 ^ 64)) with (Z_to_bv 64 a); [reflexivity|].
apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
rewrite Z.mod_mod by lia. reflexivity.
Qed.

Lemma mkl_keep : MKL_KEEP.
Proof.
intros n v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest ov vl vv regs1' memc' mdc' Pz HB HJ' HPz KM (z & Hz) HK.
destruct HB as (HCX & HLS & HFRM & HCORE & HCELLS & HREGS & Hn & Hne & HLOOP & Hovl & Hvv & HNP & H24 & H22).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HCORE as (HJ & _ & _ & VSH & _).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfr & _).
assert (Hin : In (1, pos) (frames Sc)) by (rewrite Hfr; left; reflexivity).
destruct (frames_bounds SEGS B LAWS lyc Sc Wc memc mdc 1 pos HAR Hin) as (Hf1 & Hf2 & Hf3).
change (fs_frame_bytes 1) with 128 in Hf2, Hf3.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hf3.
assert (K : forall a, 0 <= a < 2 ^ 64 -> ~ mf_win (frame_addr lyc 1 pos) (flag_addr lyc 1 pos) a ->
  rdW Wc memc' a = rdW Wc memc a).
{ intros a Ha Hw. apply KM; [exact Ha|]. intros ->. apply Hw. left. lia. }
assert (G : forall a, rdW Wc memc a <> None -> rdW Wc memc' a <> None).
{ intros a Ha. rewrite mkl_aview_mod. rewrite mkl_aview_mod in Ha.
  pose proof (Z.mod_pos_bound a (2 ^ 64) ltac:(lia)) as Hm.
  destruct (Z.eq_dec (a mod 2 ^ 64) Pz) as [E|E].
  - rewrite E, Hz. discriminate.
  - rewrite KM by lia. exact Ha. }
assert (VSH' : forall i, 4 <= i < 12 ->
  val_mem SEGS (mrestrict (w_H Wc) memc') (SHADOW_OFF + frame_addr lyc 1 pos / 8 + i) 1 MF_LOW_ON).
{ intros i Hi. apply (val_mem_moved SEGS (w_H Wc) (w_H Wc) memc memc' (SHADOW_OFF + frame_addr lyc 1 pos / 8 + i)
    (SHADOW_OFF + frame_addr lyc 1 pos / 8 + i) 1 MF_LOW_ON); [|exact (VSH i Hi)].
  intros k Hk. change (Z.of_nat 1) with 1 in Hk.
  pose proof (Z.div_mod (frame_addr lyc 1 pos) 8 ltac:(lia)) as DM.
  pose proof (Z.mod_pos_bound (frame_addr lyc 1 pos) 8 ltac:(lia)) as MB.
  apply KM; unfold SHADOW_OFF in *; lia. }
split; [exact HCX|]. split; [exact HLS|]. split; [exact HFRM|].
split; [exact (mf_tx_core B v lyc Sc Wc memc mdc memc' mdc' pos MF_LOW_ON MF_LOW_ON mcc HCX HCORE HJ' K G VSH')|].
split; [exact (mf_tx_cells B v lyc Sc Wc memc mdc memc' pos MF_LOW_ON mcc (Some gi) HCX HCORE K HCELLS)|].
split; [apply (mf_regs_at_of B v lyc pos regs1 regs1' HREGS); apply HK; cbv [MKL_KEPT In]; tauto|].
split; [exact Hn|]. split; [exact Hne|].
split; [exact (mf_tx_loop B v lyc Sc Wc memc mdc memc' mdc' pos MF_LOW_ON mcc mcc (Some gi) line p rest HCX HCORE
  (proj1 HJ') K G HLOOP)|].
split; [exact Hovl|]. split; [exact Hvv|].
split; [exact (mf_tx_np B v lyc Sc Wc memc mdc memc' pos MF_LOW_ON mcc (mf_next p rest) HCX HCORE K HNP)|].
split; [rewrite (HK 24%bv) by (cbv [MKL_KEPT In]; tauto); exact H24|].
rewrite (HK 22%bv) by (cbv [MKL_KEPT In]; tauto). exact H22.
Qed.

(* MK_FOLD with k = ln - i passes left *)
Definition mkl_n (n k : nat) : Prop :=
forall v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest ov vl vv i,
(mk_ln vl - i = k)%nat ->
mk_base B n v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest ov vl vv ->
mf_fin (mk_mod mcc gi vv (line + 1), Some gi) line rest = mf_final v ->
(i < mk_ln vl)%nat ->
sa_zs (rdW Wc memc) (frame_addr lyc 1 pos + 32) (map lower (firstn i vv)) ->
getr regs1 20 = w64 (Z.of_nat (mk_ln vl)) ->
getr regs1 21 = w64 (p + Z.of_nat (ov + i)) -> getr regs1 10 = w64 (p + Z.of_nat (ov + i)) ->
getr regs1 11 = w64 (frame_addr lyc 1 pos + 32 + Z.of_nat i) ->
getr regs1 12 = w64 (frame_addr lyc 1 pos + 32 + Z.of_nat i) ->
getr regs1 13 = w64 (Z.of_nat (mk_ln vl - i)) ->
mf_at B v Wc regs1 memc mdc MK_FOLD.

(* after a run (TRAP 1 first): the environment still agrees with the seed's E0 below 33 (HAE), and the memory with
   memc off P (KM) *)
Ltac mkl_after E0 P E11 HAE KM :=
  let mdv := fresh "mdv" in
  set (mdv := with_vm_backing _ _ _) in *; clearbody mdv;
  lazymatch goal with
  | HS : st_ok_pi _ _ ?En _ (restrict _ ?msn), HFr : frame_of ?Eo _ (mrestrict _ _) (mrestrict _ (ms_mem ?msn)) |- _ =>
    let U := fresh "U11" in
    assert (U : bv_unsigned (ew Eo 11) = P) by (apply (mkl_u11 _ _ _ HAE E11); lia);
    let HAEn := fresh "HAEn" in let KMn := fresh "KMn" in
    assert (HAEn : env_agree 33 E0 En) by (env_agree_chain HAE);
    pose proof (mkl_keep_step Eo _ _ _ _ _ _ P HFr U KM) as KMn;
    clear U HFr HAE KM; rename HAEn into HAE; rename KMn into KM;
    repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end
  end.
Ltac mkl_awr_tac HAE E11 :=
  apply mkl_awr; rewrite (mkl_u11 _ _ _ HAE E11 ltac:(lia)); change (fs_frame_bytes 1) with 128; lia.
Ltac mkl_reg_eq N := rewrite N; unfold w64; f_equal; lia.

(* one pass: MK_FOLD back to MK_FOLD with one more byte folded, or the exit to MK_FEXIT *)
Lemma mkl_step : MKL_KEEP -> forall n, MK_FEXIT_stmt B n -> forall k, mkl_n n k -> mkl_n n (S k).
Proof.
intros KEEPL n HEXIT k IH v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest ov vl vv i
  Hk HB HFIN Hi HZS0 H20 H21 H10 H11 H12 H13.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (mkl_base_facts n v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest ov vl vv HB)
  as (HF1 & HF2 & Happ & HFp & HRAL & HTX & HSTR & HRAT & HLV & HOVR & H18).
pose proof HB as (_ & _ & _ & HCORE & _ & _ & _ & _ & _ & _ & Hvv & _).
pose proof HCORE as (HJ & _).
assert (Hln : (mk_ln vl <= 23)%nat) by (unfold mk_ln; lia).
assert (Hivl : (i < vl)%nat) by (unfold mk_ln in Hi; lia).
destruct (HTX (ov + i)%nat ltac:(lia)) as (HA1 & HA2 & HA3).
(* the value byte at A = p + ov + i *)
assert (HCz : rdW Wc memc (p + Z.of_nat (ov + i)) = Some (nth i vv 0)).
{ rewrite <- Hvv, mkl_nth_firstn, mkl_nth_skipn by lia.
  destruct HSTR as [[HZ _] _]. rewrite <- (app_nth1 rest [0] 0) by lia. apply HZ. rewrite length_app. cbn [length]. lia. }
destruct (aview_byte SEGS (w_H Wc) memc _ _ HCz) as (bz & _ & _ & HCr).
set (F := frame_addr lyc 1 pos) in *.
assert (Happ' := Happ). unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ'.
set (A := p + Z.of_nat (ov + i)) in *.
assert (HAd : A = p + Z.of_nat (ov + i)) by reflexivity.
set (P := F + 32 + Z.of_nat i) in *.
assert (HPd : P = F + 32 + Z.of_nat i) by reflexivity.
set (Cz := nth i vv 0) in *.
assert (HPr : apresent (w_H Wc) memc P) by (apply HFp; lia).
pose proof (mkl_entry Wc regs1 memc A P Cz H10 H21 H11 H12 H18 ltac:(lia) ltac:(lia) ltac:(lia) HCz HPr ltac:(lia)) as HS.
pose proof (mkl_shok Wc regs1 memc P Cz H18 H11 ltac:(lia)
  (range_addressable_sub _ _ (F + 32) 64 P 1 HRAL ltac:(lia) ltac:(lia)) ltac:(unfold SB; lia)) as SHOK.
assert (HEI : img_env VAL A_LIM (mkl_E regs1 Cz)) by (unfold mkl_E; apply Eimg_env).
pose proof (mkl_env_agree regs1 Cz) as HA0.
assert (E10 : ew (mkl_E regs1 Cz) 10 = Z_to_bv 64 A) by (rewrite (mkl_ew_reg regs1 Cz 10 10%bv eq_refl); exact H10).
assert (E11 : ew (mkl_E regs1 Cz) 11 = Z_to_bv 64 P) by (rewrite (mkl_ew_reg regs1 Cz 11 11%bv eq_refl); exact H11).
assert (E13 : ew (mkl_E regs1 Cz) 13 = Z_to_bv 64 (Z.of_nat (mk_ln vl - i)))
  by (rewrite (mkl_ew_reg regs1 Cz 13 13%bv eq_refl); exact H13).
assert (E18 : ew (mkl_E regs1 Cz) 18 = Z_to_bv 64 SB) by (rewrite (mkl_ew_reg regs1 Cz 18 18%bv eq_refl); exact H18).
pose proof (mkl_ew32 regs1 Cz) as E32.
revert HS SHOK HEI HA0 E10 E11 E13 E18 E32.
generalize (mkl_E regs1 Cz) as E0.
intros E0 HS SHOK HEI HA0 E10 E11 E13 E18 E32.
pose proof (env_agree_refl 33 E0) as HAE.
assert (KM : forall a, 0 <= a < 2 ^ 64 -> a <> P -> rdW Wc memc a = rdW Wc memc a) by (intros; reflexivity).
unfold mf_at.
(* 0x867f8 .. 0x86844: the check of v[i] (an obligation), the check of low[i] (the entry), the load, the fold, the
   store, the increments, up to `bnez a3` *)
paj_run_tok RUN HS HJ SHOK Bspan.
{ cbn [ms_mem]. unfold mkl_Bx. rewrite (U_atom _ 18 SB E18), (U_atom _ 10 _ E10) by (unfold SB; lia).
  rewrite SB_SHADOW_OFF.
  exact (range_addressable_sub _ _ p (Z.of_nat (length rest) + 1) A 1 HRAT ltac:(lia) ltac:(lia)). }
{ mkl_awr_tac HAE E11. }
mkl_after E0 P E11 HAE KM.
psrr_branch_tok RUN BR HS SHOK Bspan.
- (* a3 - 1 <> 0: back to MK_FOLD *)
  pose proof (mkl_br _ _ _ (mkl_ag_ew _ _ 13 _ HAE ltac:(lia) E13) ltac:(lia) Hc) as Hnz. clear Hc.
  apply negb_true_iff, Z.eqb_neq in Hnz.
  paj_run_to_tok RUNTO HS HJ SHOK Bspan MK_FOLD. { mkl_awr_tac HAE E11. }
  mkl_after E0 P E11 HAE KM.
  pose proof (mkl_wbyte _ _ _ _ P mkl_wv HS ltac:(vm_compute; reflexivity) (mkl_u11 _ _ _ HAE E11 ltac:(lia))) as HWB.
  rewrite (mkl_store _ Cz (mkl_ag_ew _ _ 32 _ HAE ltac:(lia) E32) ltac:(lia)) in HWB.
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs1 _ MKL_KEPT HS (mkl_ag32 _ _ _ _ HA0 HAE) ltac:(vm_compute; reflexivity)) as HK.
  cbn [ms_regs restrict] in HK.
  prreg HS (10%bv : bv 5) N10; prreg HS (11%bv : bv 5) N11; prreg HS (12%bv : bv 5) N12;
  prreg HS (13%bv : bv 5) N13; prreg HS (21%bv : bv 5) N21.
  rewrite E10, unsigned_lit_small in N10, N21 by lia. rewrite E11, unsigned_lit_small in N11, N12 by lia.
  rewrite E13, unsigned_lit_small in N13 by lia.
  pmkst HS.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdn) _ =>
  assert (HB' : mk_base B n v lyc Sc Wc rg mm mdn pos mcc gi line p rest ov vl vv)
    by (exact (KEEPL n v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest ov vl vv rg mm mdn P HB HJ ltac:(lia) KM
          (ex_intro _ _ HWB) HK));
  exact (IH v lyc Sc Wc rg mm mdn pos mcc gi line p rest ov vl vv (S i) ltac:(lia) HB' HFIN ltac:(lia)
    (mkl_zs_ext _ _ F vv i P ltac:(lia) HPd ltac:(lia) ltac:(lia) HZS0 KM HWB)
    ltac:(rewrite (HK 20%bv) by (cbv [MKL_KEPT In]; tauto); exact H20)
    ltac:(mkl_reg_eq N21) ltac:(mkl_reg_eq N10) ltac:(mkl_reg_eq N11) ltac:(mkl_reg_eq N12) ltac:(mkl_reg_eq N13))
  end.
- (* a3 - 1 = 0: i + 1 = ln, the fold is done; `j` to MK_FEXIT *)
  pose proof (mkl_br _ _ _ (mkl_ag_ew _ _ 13 _ HAE ltac:(lia) E13) ltac:(lia) Hc) as Hz. clear Hc.
  apply negb_false_iff, Z.eqb_eq in Hz.
  assert (HlnS : mk_ln vl = S i) by lia.
  paj_run_to_tok RUNTO HS HJ SHOK Bspan MK_FEXIT. { mkl_awr_tac HAE E11. }
  mkl_after E0 P E11 HAE KM.
  pose proof (mkl_wbyte _ _ _ _ P mkl_wv HS ltac:(vm_compute; reflexivity) (mkl_u11 _ _ _ HAE E11 ltac:(lia))) as HWB.
  rewrite (mkl_store _ Cz (mkl_ag_ew _ _ 32 _ HAE ltac:(lia) E32) ltac:(lia)) in HWB.
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs1 _ MKL_KEPT HS (mkl_ag32 _ _ _ _ HA0 HAE) ltac:(vm_compute; reflexivity)) as HK.
  cbn [ms_regs restrict] in HK.
  pmkst HS.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdn) _ =>
  assert (HB' : mk_base B n v lyc Sc Wc rg mm mdn pos mcc gi line p rest ov vl vv)
    by (exact (KEEPL n v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest ov vl vv rg mm mdn P HB HJ ltac:(lia) KM
          (ex_intro _ _ HWB) HK));
  assert (HZF : sa_zs (rdW Wc mm) (F + 32) (h_fold vv 24))
    by (rewrite <- hfold_firstn, HLV, HlnS; exact (mkl_zs_ext _ _ F vv i P ltac:(lia) HPd ltac:(lia) ltac:(lia) HZS0 KM HWB));
  exact (HEXIT v lyc Sc Wc rg mm mdn pos mcc gi line p rest ov vl vv HB' HFIN HZF
    ltac:(rewrite (HK 20%bv) by (cbv [MKL_KEPT In]; tauto); exact H20))
  end.
Qed.

(* MK_FOLD from MK_FEXIT, given the keep fact of a pass *)
Lemma mkl_fold_of_keep : MKL_KEEP -> forall n, MK_FEXIT_stmt B n -> MK_FOLD_stmt B n.
Proof.
intros KEEPL n HEXIT.
assert (ALL : forall k, mkl_n n k).
{ induction k as [|k IHk].
  - intros v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest ov vl vv i Hk _ _ Hi. lia.
  - exact (mkl_step KEEPL n HEXIT k IHk). }
unfold MK_FOLD_stmt.
intros v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest ov vl vv i HB HFIN Hi HZS H20 H21 H10 H11 H12 H13.
exact (ALL (mk_ln vl - i)%nat v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest ov vl vv i eq_refl HB HFIN Hi HZS
  H20 H21 H10 H11 H12 H13).
Qed.

(* the fold loop of S_MF_KMOD: MK_FOLD 0x867f8 from MK_FEXIT 0x86864 *)
Lemma mk_fold_ok : forall n, MK_FEXIT_stmt B n -> MK_FOLD_stmt B n.
Proof. exact (mkl_fold_of_keep mkl_keep). Qed.

End e.
End f.
End d.
Print Assumptions mk_fold_ok.

