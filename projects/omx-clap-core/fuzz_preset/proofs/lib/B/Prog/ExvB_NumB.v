(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Does not rest on tex_word_specX; memnorm only through EXN_keepM's keep premise, the identity here (kit 4f18c75d4900). *)
(* Theorem Labs, 2026-10: fuzz_preset, image B (asan-ubsan, rebuilt pin f8f98a95bc52, unstripped twin 3b5e1a099b53),
   ex_value's NUMBER SEGMENT, sub-piece Bp (lib/B/Prog/ExvB_NumCut.v EXN_Bl): the scan loop, CL (exv_pc 0x324,
   B 0x83850) to CS (exv_pc 0x84c, B 0x83d78), by induction on the bytes left (length x - j), as ex_ws_x.v's
   pb_ex_wsX_loop walks ex_ws's loop (its engine helpers taken from ExvB_Num_eng.v). Proves no function (kind: segment
   lemma).
   Code (neutral listing, the internal file ex_value.fuzz_preset.asan-ubsan.s, a Theorem Labs lane's listing of the B' pin, lines 203-221 and
   532; never a raw disassembly):
     0x83850 srli a6,a0,3 / add a6,a6,s9 / lb a6,0(a6) / bnez a6 -> 0x83890   the shadow byte of a0 = x0 + j
     0x83890 andi a7,a0,7 / blt a7,a6 -> 0x83860 / jal errpath_load1           partial-granule slow path
     0x83860 lbu a6,0(s6)                                                      x[j]
     0x83864 addi a7,a6,-58 / bltu a3(-11),a7 -> 0x83880                       digit: take
     0x8386c addi a6,a6,-43 / bltu a4(58),a6 -> 0x83d78                        out of the class range: stop
     0x83874 srl a6,a5,a6 / andi a6,a6,1 / beqz a6 -> 0x83d78                  the mask bit clear: stop
     0x83880 addi s6,s6,1 / addi a0,a0,1 / bne s6,a2 -> 0x83850 / j 0x83d74   next byte, or the text's end
     0x83d74 mv s6,a2                                                          the end exit, falls into CS
   The shadow check and its slow path are taken by the table runner's shadow tokens (YCbn.v tok_load / tok_branch)
   from ONE shadow entry, [x0 + j, x0 + j + 1), whose fact is src_rd's range_addressable of the text: the slow path
   returns to 0x83860 inside the run and `jal errpath_load1` is never reached. The three-test class decision is
   ExvB_NumPure.v's exn_scan_ok_numch. The loop writes no memory (no write window), so the state's memory is the cut's
   (functional extensionality, allowlisted), EXB moves to the new registers through EXN_keepM (its memnorm keep premise
   is the identity, memc' = memc) and the two spills, the cursor and the frame shadow ride through unchanged. The first
   pass reads the lead digit (EXN_span), so a stop is at j > i1 + sg, the strict bound of EXN_CS_pre.
   Image A's proved walk of the same loop (exv/s8a/S8aNumB.v) was read for the proof shape only; nothing of it is
   Required or cited.
   Numerals: 0x324, 0x84c (DERIVED: cut offsets, through EXN_CL / EXN_CS); -11, 58, -58, 43, -43, 1, 0 (WORD: the
   listing's immediates and branch operands as the runner leaves them); 2, 3, 4, 8, 9, 10, 11, 12, 13, 14, 15, 18, 19,
   21, 22, 23, 24, 25, 26, 27 (WORD: register numbers); 32 (LENGTH: the runner's first extra atom, and the register
   count of env_agree); 5 (LENGTH: the register index width); 4096, 2 ^ 47 - 1, 255, 256, 2 ^ 64, 63, 64, 8
   (LENGTH / DERIVED: address-space bound, byte range and modulus, word modulus, the ALU model's shift mask and width,
   widths). No ADDRESS: every pc is exv_pc of a DERIVED offset; the hex addresses above name listing lines only. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From Stdlib Require FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YG0s YP07 YI00 YI16.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YK06.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0d YP0c YC80 YPsym YC4aP YImgTop YC1fP YCbqG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YGcfRoomKeep FCiface.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_FnEx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Img0 Listing_prog PAImg_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import
ExvB_Stmt ExvB_Num_eng ExvB_NumPure ExvB_NumCut.
Import ListNotations.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

#[local] Existing Instance prh_img_B.

(* ---- the symbolic state at CL: a0 the atom of s6 (x0 + j), the loop constants a3 a4 a5 literal, s9 the shadow base
   (atom 25, fact SHADOW_OFF), x[j] the one-byte read-only region at s6 holding atom 32 (the env's extra word) ---- *)
Definition EXNB_SB : sv := SOff 25 0.
Definition exnb_regs : list sv :=
  sr_set (sr_set (sr_set (sr_set sr_atoms 10%bv (SOff 22 0)) 13%bv (SLit (-11))) 14%bv (SLit 58)) 15%bv (SLit exn_MASK).
Definition exnb_mem : smem := [YP09.mkRegion (Some 22%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 32 0))]].
Definition exnb_facts : list (nat * afact) :=
  [(22%nat, mkAF 4096 (2 ^ 47 - 1) 0); (25%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (32%nat, mkAF 0 255 0)].
Definition ss_exnb : sstate := mkSS (exv_pc EXN_CL) exnb_regs exnb_mem None (mkFacts exnb_facts [] []).
Definition exnb_SH : list shent := [mkSHE 22 0 1].
(* the registers the loop never writes that CL / CS / EXB name *)
Definition EXNB_KEPT : list (bv 5) := [2; 3; 4; 8; 9; 11; 12; 18; 19; 21; 23; 24; 25; 26; 27]%bv.
Ltac exnb_in := cbv [EXNB_KEPT]; cbn [In]; repeat first [left; reflexivity | right].

(* the three shapes a pass ends in: back at CL with s6 = a0 = x0 + j + 1; at CS with s6 = x0 + j (a stop byte); at CS
   through 0x83d74 with s6 = a2 = x0 + len *)
Definition exnb_kept_ok (ss : sstate) : bool :=
  forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) EXNB_KEPT.
Definition exnb_resv_none (ss : sstate) : bool := match ss_resv ss with None => true | Some _ => false end.
Definition exnb_shape_loop (ss : sstate) : bool :=
  (ss_pc ss =? exv_pc EXN_CL) && exnb_resv_none ss && exnb_kept_ok ss &&
  sv_eqb (sr_get (ss_regs ss) 22%bv) (SOff 22 1) && sv_eqb (sr_get (ss_regs ss) 10%bv) (SOff 22 1) &&
  sv_eqb (sr_get (ss_regs ss) 13%bv) (SLit (-11)) && sv_eqb (sr_get (ss_regs ss) 14%bv) (SLit 58) &&
  sv_eqb (sr_get (ss_regs ss) 15%bv) (SLit exn_MASK).
Definition exnb_shape_stop (ss : sstate) : bool :=
  (ss_pc ss =? exv_pc EXN_CS) && exnb_resv_none ss && exnb_kept_ok ss &&
  sv_eqb (sr_get (ss_regs ss) 22%bv) (SOff 22 0).
Definition exnb_shape_end (ss : sstate) : bool :=
  (ss_pc ss =? exv_pc EXN_CS) && exnb_resv_none ss && exnb_kept_ok ss &&
  sv_eqb (sr_get (ss_regs ss) 22%bv) (SOff 12 0).

(* ---- pure: the runner's three branch conditions as ExvB_NumPure's tests ---- *)
Lemma exnb_ult : forall Ev n v x o, ew Ev n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  (U Ev (SLit x) <? U Ev (SOff n o)) = exn_ult x (v + o).
Proof.
intros Ev n v x o H Hv. rewrite U_SLit, U_SOff, H, unsigned_lit_small by lia.
unfold zcanon, exn_ult, M64, exn_M64. reflexivity.
Qed.

Lemma exnb_mask_U : forall Ev b M, ew Ev 32 = Z_to_bv 64 b -> 0 <= b < 256 -> M = exn_MASK ->
  U Ev (SAlu ALU_AND (SAlu ALU_SRL (SLit M) (SOff 32 (-43))) (SLit 1)) =
  (if Z.testbit exn_MASK ((b - 43) mod exn_M64 mod 64) then 1 else 0).
Proof.
intros Ev b M H Hb ->. rewrite !U_SAlu, U_SOff, H, unsigned_lit_small by lia.
rewrite !U_lit by (rewrite ?exn_MASK_value; lia).
assert (A : forallb (fun y => Z.eqb
  (zcanon (zalu_raw 63 64 ALU_AND (zcanon (zalu_raw 63 64 ALU_SRL exn_MASK (zcanon (y + -43)))) 1))
  (if Z.testbit exn_MASK ((y - 43) mod exn_M64 mod 64) then 1 else 0)) exn_bytes256 = true)
  by (vm_compute; reflexivity).
apply Z.eqb_eq. exact (exn_forallb_bytes256 _ A b Hb).
Qed.

Lemma exnb_numch_split : forall b, 0 <= b < 256 ->
  PjGrammar.numch b = exn_ult (-11) (b - 58) ||
    (negb (exn_ult 58 (b - 43)) && Z.testbit exn_MASK ((b - 43) mod exn_M64 mod 64)).
Proof. intros b Hb. rewrite <- (exn_scan_ok_numch b Hb). reflexivity. Qed.

Lemma exnb_digit_numch : forall b, PjGrammar.digit b = true -> PjGrammar.numch b = true.
Proof. intros b H. unfold PjGrammar.numch. rewrite H. reflexivity. Qed.

(* ---- pure: the span grows by one numch byte ---- *)
Lemma exnb_firstn_S : forall (l : list Z) n, (n < length l)%nat -> firstn (S n) l = firstn n l ++ [nth n l 0].
Proof.
induction l as [|h t IH]; intros n Hn; [cbn in Hn; lia|].
destruct n as [|n]; [reflexivity|].
cbn [firstn nth app]. f_equal. apply IH. cbn in Hn. lia.
Qed.

Lemma exnb_nth_skipn : forall (l : list Z) n m, nth m (skipn n l) 0 = nth (n + m) l 0.
Proof.
induction l as [|h t IH]; intros n m.
- rewrite skipn_nil. destruct m, n; reflexivity.
- destruct n as [|n]; cbn [skipn]; [reflexivity | exact (IH n m)].
Qed.

Lemma exnb_span_step : forall E c j, (EXN_i1 E + exn_sg c <= j < length (e_x E))%nat ->
  EXN_span E c j -> PjGrammar.numch (nth j (e_x E) 0) = true -> EXN_span E c (S j).
Proof.
intros E c j Hj HSP Hn. unfold EXN_span in *. destruct HSP as (H1 & H2 & H3 & HF).
refine (conj H1 (conj H2 (conj H3 _))). unfold exn_sub in *.
replace (S j - (EXN_i1 E + exn_sg c))%nat with (S (j - (EXN_i1 E + exn_sg c))) by lia.
rewrite exnb_firstn_S by (rewrite length_skipn; lia).
apply Forall_app. split; [exact HF|]. constructor; [|constructor].
rewrite exnb_nth_skipn. replace (EXN_i1 E + exn_sg c + (j - (EXN_i1 E + exn_sg c)))%nat with j by lia. exact Hn.
Qed.

(* ---- the loop writes nothing: a pass keeps the whole memory ---- *)
Lemma exnb_frame : forall Ev rs (m m' : word -> option byte), frame_of Ev rs m m' -> rs = exnb_mem -> m' = m.
Proof.
intros Ev rs m m' HF Hrs. apply FunctionalExtensionality.functional_extensionality. intros x. apply HF. subst rs.
intros (r & Hin & Hr). unfold exnb_mem in Hin. destruct Hin as [<-|[]]. cbn [YP09.r_wlo YP09.r_whi] in Hr. lia.
Qed.

Ltac exnb_awr :=
  lazymatch goal with |- awr_ok ?Ex ?rs _ _ _ _ _ _ _ =>
    let rs' := eval vm_compute in rs in change rs with rs' end;
  repeat (apply exw_awr_cons; [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia | ]);
  apply awr_ok_nil.

(* after a run (ExvB_Num_eng.v's exw_after_run names the frame facts HF / HFr / HG): Hm, the memory is the cut's *)
Ltac exnb_mem_clear :=
  repeat match goal with H' : frame_of _ _ _ _ |- _ => clear H' | H' : mem_grows _ _ |- _ => clear H' end.
Ltac exnb_mem0 HF Hm :=
  pose proof (exnb_frame _ _ _ _ HF ltac:(vm_compute; reflexivity)) as Hm; clear HF; exnb_mem_clear.
Ltac exnb_mem HF Hm :=
  let H := fresh "Hmem" in
  pose proof (exnb_frame _ _ _ _ HF ltac:(vm_compute; reflexivity)) as H; clear HF;
  rewrite Hm in H; clear Hm; rename H into Hm; exnb_mem_clear.

Section p. Context {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world rsegs -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
Variable E : exv_e.
Variable pos : Z.
Hypothesis HYP : EXV_HYP B ARx SK.
Hypothesis HC : EXN_C B ARx SK E pos.
Hypothesis MK : EXN_keepM B ARx SK E pos.
Hypothesis KS : EXN_keep_spill E.

#[local] Abbreviation AJ lyc Sc Hpc Wc memc mdc k :=
  (ajournal_x (SK := SK) rsegs B prh_pst ARx (exv_STK E + e_d E) (exv_sp E + e_d E) (exv_FP E)
     (e_ly E) (e_S E) (e_Hp E) (e_W E) (e_mem E) (e_md E) [(1, pos)] lyc Sc Hpc Wc memc mdc k).

(* the loop statement at m bytes left *)
Definition exnb_KL (m : nat) : Prop :=
  forall fxc lyc Sc Hpc Wc regs memc mdc k c j,
  (length (e_x E) - j)%nat = m -> EXV_PRE B ARx E ->
  EXN_CL_pre B ARx SK E pos fxc lyc Sc Hpc Wc regs memc mdc k c j ->
  SRr rsegs Wc (cfg_at (fx := fxc) rsegs (exv_pc EXN_CL) regs memc mdc) (EXV_POST B ARx SK E).

(* EXB at the pass's last registers: the memory is the cut's, the journal the run's *)
Lemma exnb_base_keep : forall fxc lyc Sc Hpl Wc regs memc mdc k regs' mdc',
  EXV_PRE B ARx E -> EXN_base B ARx SK E pos fxc lyc Sc Hpl Wc regs memc mdc k ->
  AJ lyc Sc Hpl Wc memc mdc' k ->
  (forall r, In r EXNB_KEPT -> YK11.getr regs' r = YK11.getr regs r) ->
  EXN_base B ARx SK E pos fxc lyc Sc Hpl Wc regs' memc mdc' k.
Proof.
intros fxc lyc Sc Hpl Wc regs memc mdc k regs' mdc' HPRE (HB & HS144 & HS152) HJ HK.
split; [|exact (conj HS144 HS152)].
apply (MK fxc lyc Sc Hpl Wc regs memc mdc k regs' memc mdc' k HPRE HB HJ).
- intros z _ _. reflexivity.
- intros a Ha. exact Ha.
- intros Hn. exact Hn.
- unfold EXN_regs_kept. repeat split; apply HK; exnb_in.
Qed.

(* ---- closing a pass at a cut, from the runner's state and its shape ---- *)
Lemma exnb_close_loop : forall m fxc lyc Sc Hpl Wc regs memc mdc k c j extra Ev ss ms md',
  exnb_KL m -> (length (e_x E) - j)%nat = S m -> EXV_PRE B ARx E ->
  EXN_CL_pre B ARx SK E pos fxc lyc Sc Hpl Wc regs memc mdc k c j ->
  st_ok (fx := fxc) rsegs Ev ss (restrict (w_H Wc) ms) -> exnb_shape_loop ss = true ->
  env_agree 32 (Ereg regs extra) Ev -> ms_mem ms = memc -> AJ lyc Sc Hpl Wc (ms_mem ms) md' k ->
  PjGrammar.numch (nth j (e_x E) 0) = true -> (S j < length (e_x E))%nat ->
  SRr rsegs Wc (mkCfg ms md') (EXV_POST B ARx SK E).
Proof.
intros m fxc lyc Sc Hpl Wc regs memc mdc k c j extra Ev ss ms md' IH Hmj HPRE HCL HS Hsh HA Hm HJ Hn Hlt.
unfold exnb_shape_loop in Hsh. repeat rewrite andb_true_iff in Hsh.
destruct Hsh as [[[[[[[Hpcq Hrv] Hkp] S22] S10] S13] S14] S15].
apply Z.eqb_eq in Hpcq.
assert (Hrv' : ss_resv ss = None) by (unfold exnb_resv_none in Hrv; destruct (ss_resv ss); [discriminate | reflexivity]).
pose proof (st_ok_restrict_mkst rsegs _ _ _ _ HS Hrv') as Hms.
pose proof (regs_kept_of_st_ok rsegs _ _ _ regs extra EXNB_KEPT HS HA Hkp) as HK. cbn [ms_regs restrict] in HK.
pose proof HCL as (HBASE & HDISP & HCUR & HFSH & HSPAN & Hj & R27 & R22 & R10 & R11 & R12 & R21 & R23 & R13 & R14 &
  R15 & HS136).
pose proof HBASE as (HB & _ & _).
pose proof HB as HB'. unfold EXB in HB'. cbv zeta in HB'.
destruct HB' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSRC & _).
pose proof HSRC as (_ & Hx0lo & Hx0hi & _).
pose proof (@alloc_ceiling_lt rc) as Hceil.
destruct HA as [HA0 _].
assert (E22 : ew Ev 22 = Z_to_bv 64 (e_x0 E + Z.of_nat j)).
{ rewrite HA0 by lia. rewrite (ew_Ereg_nat regs extra 22 22%bv eq_refl). exact R22. }
pose proof (st_ok_restrict_reg rsegs _ _ _ _ 22%bv HS) as Q22. rewrite (sv_eqb_eq _ _ S22) in Q22.
pose proof (st_ok_restrict_reg rsegs _ _ _ _ 10%bv HS) as Q10. rewrite (sv_eqb_eq _ _ S10) in Q10.
pose proof (st_ok_restrict_reg rsegs _ _ _ _ 13%bv HS) as Q13. rewrite (sv_eqb_eq _ _ S13) in Q13.
pose proof (st_ok_restrict_reg rsegs _ _ _ _ 14%bv HS) as Q14. rewrite (sv_eqb_eq _ _ S14) in Q14.
pose proof (st_ok_restrict_reg rsegs _ _ _ _ 15%bv HS) as Q15. rewrite (sv_eqb_eq _ _ S15) in Q15.
cbn [sv_denot] in Q22, Q10, Q13, Q14, Q15.
rewrite E22, unsigned_lit_small in Q22, Q10 by lia.
rewrite Hms, Hpcq, Hm. rewrite Hm in HJ.
refine (IH fxc lyc Sc Hpl Wc (ms_regs ms) memc md' k c (S j) ltac:(lia) HPRE _).
unfold EXN_CL_pre.
refine (conj _ (conj HDISP (conj HCUR (conj HFSH (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _
  (conj _ (conj _ (conj _ (conj _ HS136)))))))))))))))).
- exact (exnb_base_keep fxc lyc Sc Hpl Wc regs memc mdc k (ms_regs ms) md' HPRE HBASE HJ HK).
- exact (exnb_span_step E c j ltac:(lia) HSPAN Hn).
- lia.
- rewrite (HK 27%bv ltac:(exnb_in)). exact R27.
- rewrite Q22. unfold w64. f_equal. lia.
- rewrite Q10. unfold w64. f_equal. lia.
- rewrite (HK 11%bv ltac:(exnb_in)). exact R11.
- rewrite (HK 12%bv ltac:(exnb_in)). exact R12.
- rewrite (HK 21%bv ltac:(exnb_in)). exact R21.
- rewrite (HK 23%bv ltac:(exnb_in)). exact R23.
- exact Q13.
- exact Q14.
- exact Q15.
Qed.

Lemma exnb_close_stop : forall fxc lyc Sc Hpl Wc regs memc mdc k c j extra Ev ss ms md',
  EXV_PRE B ARx E -> EXN_CL_pre B ARx SK E pos fxc lyc Sc Hpl Wc regs memc mdc k c j ->
  st_ok (fx := fxc) rsegs Ev ss (restrict (w_H Wc) ms) -> exnb_shape_stop ss = true ->
  env_agree 32 (Ereg regs extra) Ev -> ms_mem ms = memc -> AJ lyc Sc Hpl Wc (ms_mem ms) md' k ->
  PjGrammar.numch (nth j (e_x E) 0) = false ->
  SRr rsegs Wc (mkCfg ms md') (EXV_POST B ARx SK E).
Proof.
intros fxc lyc Sc Hpl Wc regs memc mdc k c j extra Ev ss ms md' HPRE HCL HS Hsh HA Hm HJ Hn.
unfold exnb_shape_stop in Hsh. repeat rewrite andb_true_iff in Hsh.
destruct Hsh as [[[Hpcq Hrv] Hkp] S22].
apply Z.eqb_eq in Hpcq.
assert (Hrv' : ss_resv ss = None) by (unfold exnb_resv_none in Hrv; destruct (ss_resv ss); [discriminate | reflexivity]).
pose proof (st_ok_restrict_mkst rsegs _ _ _ _ HS Hrv') as Hms.
pose proof (regs_kept_of_st_ok rsegs _ _ _ regs extra EXNB_KEPT HS HA Hkp) as HK. cbn [ms_regs restrict] in HK.
pose proof HCL as (HBASE & HDISP & HCUR & HFSH & HSPAN & Hj & R27 & R22 & R10 & R11 & R12 & R21 & R23 & _).
pose proof HCL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HS136).
pose proof HBASE as (HB & _ & _).
pose proof HB as HB'. unfold EXB in HB'. cbv zeta in HB'.
destruct HB' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSRC & _).
pose proof HSRC as (_ & Hx0lo & Hx0hi & _).
pose proof (@alloc_ceiling_lt rc) as Hceil.
destruct HA as [HA0 _].
assert (E22 : ew Ev 22 = Z_to_bv 64 (e_x0 E + Z.of_nat j)).
{ rewrite HA0 by lia. rewrite (ew_Ereg_nat regs extra 22 22%bv eq_refl). exact R22. }
pose proof (st_ok_restrict_reg rsegs _ _ _ _ 22%bv HS) as Q22. rewrite (sv_eqb_eq _ _ S22) in Q22.
cbn [sv_denot] in Q22. rewrite E22, unsigned_lit_small, Z.add_0_r in Q22 by lia.
assert (Hj' : (EXN_i1 E + exn_sg c < j)%nat).
{ destruct (Nat.eq_dec j (EXN_i1 E + exn_sg c)) as [Ej | Nj]; [|lia].
  exfalso. pose proof HSPAN as (_ & Hd & _). rewrite <- Ej in Hd.
  rewrite (exnb_digit_numch _ Hd) in Hn. discriminate Hn. }
rewrite Hms, Hpcq, Hm. rewrite Hm in HJ.
refine (HC fxc lyc Sc Hpl Wc (ms_regs ms) memc md' k c j HPRE _).
unfold EXN_CS_pre.
refine (conj _ (conj HDISP (conj HCUR (conj HFSH (conj HSPAN (conj _ (conj (or_intror Hn) (conj _ (conj _ (conj _
  (conj _ (conj _ HS136)))))))))))).
- exact (exnb_base_keep fxc lyc Sc Hpl Wc regs memc mdc k (ms_regs ms) md' HPRE HBASE HJ HK).
- lia.
- rewrite (HK 27%bv ltac:(exnb_in)). exact R27.
- exact Q22.
- rewrite (HK 11%bv ltac:(exnb_in)). exact R11.
- rewrite (HK 21%bv ltac:(exnb_in)). exact R21.
- rewrite (HK 23%bv ltac:(exnb_in)). exact R23.
Qed.

Lemma exnb_close_end : forall fxc lyc Sc Hpl Wc regs memc mdc k c j extra Ev ss ms md',
  EXV_PRE B ARx E -> EXN_CL_pre B ARx SK E pos fxc lyc Sc Hpl Wc regs memc mdc k c j ->
  st_ok (fx := fxc) rsegs Ev ss (restrict (w_H Wc) ms) -> exnb_shape_end ss = true ->
  env_agree 32 (Ereg regs extra) Ev -> ms_mem ms = memc -> AJ lyc Sc Hpl Wc (ms_mem ms) md' k ->
  PjGrammar.numch (nth j (e_x E) 0) = true -> S j = length (e_x E) ->
  SRr rsegs Wc (mkCfg ms md') (EXV_POST B ARx SK E).
Proof.
intros fxc lyc Sc Hpl Wc regs memc mdc k c j extra Ev ss ms md' HPRE HCL HS Hsh HA Hm HJ Hn Hend.
unfold exnb_shape_end in Hsh. repeat rewrite andb_true_iff in Hsh.
destruct Hsh as [[[Hpcq Hrv] Hkp] S22].
apply Z.eqb_eq in Hpcq.
assert (Hrv' : ss_resv ss = None) by (unfold exnb_resv_none in Hrv; destruct (ss_resv ss); [discriminate | reflexivity]).
pose proof (st_ok_restrict_mkst rsegs _ _ _ _ HS Hrv') as Hms.
pose proof (regs_kept_of_st_ok rsegs _ _ _ regs extra EXNB_KEPT HS HA Hkp) as HK. cbn [ms_regs restrict] in HK.
pose proof HCL as (HBASE & HDISP & HCUR & HFSH & HSPAN & Hj & R27 & R22 & R10 & R11 & R12 & R21 & R23 & _).
pose proof HCL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HS136).
destruct HA as [HA0 _].
assert (E12 : ew Ev 12 = Z_to_bv 64 (e_x0 E + exv_len E)).
{ rewrite HA0 by lia. rewrite (ew_Ereg_nat regs extra 12 12%bv eq_refl). exact R12. }
pose proof (st_ok_restrict_reg rsegs _ _ _ _ 22%bv HS) as Q22. rewrite (sv_eqb_eq _ _ S22) in Q22.
cbn [sv_denot] in Q22. rewrite E12, Z.add_0_r, Z_to_bv_bv_unsigned in Q22.
rewrite Hms, Hpcq, Hm. rewrite Hm in HJ.
refine (HC fxc lyc Sc Hpl Wc (ms_regs ms) memc md' k c (S j) HPRE _).
unfold EXN_CS_pre.
refine (conj _ (conj HDISP (conj HCUR (conj HFSH (conj _ (conj _ (conj (or_introl Hend) (conj _ (conj _ (conj _
  (conj _ (conj _ HS136)))))))))))).
- exact (exnb_base_keep fxc lyc Sc Hpl Wc regs memc mdc k (ms_regs ms) md' HPRE HBASE HJ HK).
- exact (exnb_span_step E c j ltac:(lia) HSPAN Hn).
- lia.
- rewrite (HK 27%bv ltac:(exnb_in)). exact R27.
- rewrite Q22. unfold exv_len. rewrite <- Hend. reflexivity.
- rewrite (HK 11%bv ltac:(exnb_in)). exact R11.
- rewrite (HK 21%bv ltac:(exnb_in)). exact R21.
- rewrite (HK 23%bv ltac:(exnb_in)). exact R23.
Qed.

(* ---- one pass: CL at j -> CL at j + 1 (the induction hypothesis) or CS ---- *)
Lemma exnb_step : forall m, exnb_KL m -> exnb_KL (S m).
Proof.
intros m IH fxc lyc Sc Hpl Wc regs memc mdc k c j Hmj HPRE HCL.
pose proof HCL as (HBASE & HDISP & HCUR & HFSH & HSPAN & Hj & R27 & R22 & R10 & R11 & R12 & R21 & R23 & R13 & R14 &
  R15 & HS136).
pose proof HBASE as (HB & _ & _).
pose proof HB as HB'. unfold EXB in HB'. cbv zeta in HB'.
destruct HB' as (HJ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & R25 & _ & _ & _ & _ & _ & _ & _ & HSRC & _).
pose proof HSRC as (HG8 & Hx0lo & Hx0hi & Hamem & HRA & _).
pose proof (@alloc_ceiling_lt rc) as Hceil.
assert (Hjx : (j < length (e_x E))%nat) by lia.
destruct (HG8 j Hjx) as [Vb Hb8].
assert (Hbx : exists b, nth j (e_x E) 0 = b) by (eexists; reflexivity).
destruct Hbx as (b & Hbeq). rewrite Hbeq in Vb, Hb8.
assert (Hlen : exv_len E = Z.of_nat (length (e_x E))) by reflexivity.
remember (Ereg regs [Z_to_bv 64 b]) as Ev eqn:HE.
assert (E22 : ew Ev 22 = Z_to_bv 64 (e_x0 E + Z.of_nat j)) by (subst Ev; rewrite (ew_Ereg_nat regs _ 22 22%bv eq_refl); exact R22).
assert (E12 : ew Ev 12 = Z_to_bv 64 (e_x0 E + exv_len E)) by (subst Ev; rewrite (ew_Ereg_nat regs _ 12 12%bv eq_refl); exact R12).
assert (E25 : ew Ev 25 = Z_to_bv 64 SHADOW_OFF) by (subst Ev; rewrite (ew_Ereg_nat regs _ 25 25%bv eq_refl); exact R25).
assert (E32 : ew Ev 32 = Z_to_bv 64 b) by (subst Ev; exact (ew_Ereg_extra regs _ 0)).
assert (U22 : bv_unsigned (ew Ev 22) = e_x0 E + Z.of_nat j) by (rewrite E22; apply unsigned_lit_small; lia).
assert (U25 : bv_unsigned (ew Ev 25) = SHADOW_OFF) by (rewrite E25; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U32 : bv_unsigned (ew Ev 32) = b) by (rewrite E32; apply unsigned_lit_small; lia).
assert (HS : st_ok (fx := fxc) rsegs Ev ss_exnb
  (restrict (w_H Wc) (YK11.mkst regs (Z_to_bv 64 (exv_pc EXN_CL)) memc (YK11.seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. unfold ss_exnb. apply exw_st_ok_full.
  - unfold exnb_regs.
    apply regs_ok_pin; [| intros X; discriminate X | cbn [sv_denot]; exact R15].
    apply regs_ok_pin; [| intros X; discriminate X | cbn [sv_denot]; exact R14].
    apply regs_ok_pin; [| intros X; discriminate X | cbn [sv_denot]; exact R13].
    apply regs_ok_pin; [| intros X; discriminate X | cbn [sv_denot]; rewrite U22, Z.add_0_r; exact R10].
    subst Ev. apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - unfold exnb_mem. constructor; [|constructor]. unfold region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U22. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val rsegs Ev _ (e_x0 E + Z.of_nat j) 0 1 (SOff 32 0) b);
      [cbn [sv_denot]; rewrite U32, Z.add_0_r; reflexivity | cbn; lia | zside | rewrite Z.add_0_r; exact Vb].
  - apply pairwise_disjoint_of_extents. unfold exnb_mem. cbn [map]. unfold extent_of_region.
    cbn [zpairwise_disjoint zall_disjoint]. tauto.
  - split; [|split; [exact I | exact I]].
    cbn [f_atoms atoms_ok exnb_facts]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U22, U25, U32. rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SHADOW_OFF. repeat split; lia. }
assert (HBx : U Ev EXNB_SB = SHADOW_OFF)
  by (unfold EXNB_SB; rewrite (U_atom Ev 25 SHADOW_OFF E25) by (unfold SHADOW_OFF; lia); reflexivity).
assert (SHOK : sh_ok rsegs EXNB_SB exnb_SH Ev (mrestrict (w_H Wc) memc)).
{ unfold exnb_SH. constructor; [|constructor].
  apply (shent_ok_of_range rsegs (w_H Wc) memc Ev EXNB_SB 22 (e_x0 E) (Z.of_nat (length (e_x E)))
           (e_x0 E + Z.of_nat j) 0 1 HRA HBx);
    [rewrite (U_atom Ev 22 _ E22) by lia; reflexivity | lia | lia |].
  intros x Hx. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hamem. unfold SHADOW_OFF. lia. }
pose proof (SRr_run_tok_AJx (fx := fxc) (SK := SK) rsegs B prh_pst ARx (eh_laws B ARx SK HYP) B_prog_segs_low
  EXW_TBL B_prog_tbl_ok B_prog_wx) as RUN.
pose proof (SRr_run_to_tok_AJx (fx := fxc) (SK := SK) rsegs B prh_pst ARx (eh_laws B ARx SK HYP) B_prog_segs_low
  EXW_TBL B_prog_tbl_ok B_prog_wx) as RUNTO.
unfold cfg_at.
(* CL .. 0x83868: the shadow check of a0 (slow path inside the run), x[j], the digit test *)
exw_run RUN HS HJ SHOK.
{ exnb_awr. }
exnb_mem0 HF Hm.
exw_branch HS SHOK.
- (* a digit: 0x83880, s6 + 1, a0 + 1, `bne s6, a2` *)
  rewrite branch_ltu_U in Hc. rewrite (exnb_ult _ 32 b (-11) (-58)) in Hc by first [exw_ew E32 | lia].
  assert (Hn : PjGrammar.numch b = true).
  { rewrite (exnb_numch_split b Hb8). replace (b - 58) with (b + -58) by lia. rewrite Hc. reflexivity. }
  clear Hc.
  exw_run RUN HS HJ SHOK.
  { exnb_awr. }
  exnb_mem HF Hm.
  exw_branch HS SHOK;
    rewrite branch_ne_U, !U_SOff in Hc; cbn [ew ewset Nat.eqb] in Hc; rewrite E22, E12 in Hc;
    rewrite !unsigned_lit_small in Hc by lia; rewrite !zcanon_id in Hc by (unfold M64; lia).
  + apply negb_true_iff, Z.eqb_neq in Hc.
    exw_run_to RUNTO HS HJ SHOK (exv_pc EXN_CL).
    { exnb_awr. }
    exnb_mem HF Hm.
    lazymatch goal with HS : st_ok _ ?E' ?ss (restrict _ ?ms) |- _ =>
      apply (exnb_close_loop m fxc lyc Sc Hpl Wc regs memc mdc k c j [Z_to_bv 64 b] E' ss ms _ IH Hmj HPRE HCL HS
        ltac:(vm_compute; reflexivity) ltac:(rewrite <- HE; apply exw_agree2) Hm HJ
        ltac:(rewrite Hbeq; exact Hn) ltac:(lia))
    end.
  + apply negb_false_iff, Z.eqb_eq in Hc.
    exw_run_to RUNTO HS HJ SHOK (exv_pc EXN_CS).
    { exnb_awr. }
    exnb_mem HF Hm.
    lazymatch goal with HS : st_ok _ ?E' ?ss (restrict _ ?ms) |- _ =>
      apply (exnb_close_end fxc lyc Sc Hpl Wc regs memc mdc k c j [Z_to_bv 64 b] E' ss ms _ HPRE HCL HS
        ltac:(vm_compute; reflexivity) ltac:(rewrite <- HE; apply exw_agree2) Hm HJ
        ltac:(rewrite Hbeq; exact Hn) ltac:(lia))
    end.
- (* not a digit: the class range test b - 43 <= 58 *)
  rewrite branch_ltu_U in Hc. rewrite (exnb_ult _ 32 b (-11) (-58)) in Hc by first [exw_ew E32 | lia].
  rename Hc into Hd.
  exw_run RUN HS HJ SHOK.
  { exnb_awr. }
  exnb_mem HF Hm.
  exw_branch HS SHOK;
    rewrite branch_ltu_U in Hc; rewrite (exnb_ult _ 32 b 58 (-43)) in Hc by first [exw_ew E32 | lia].
  + (* out of the range: stop at j *)
    assert (Hn : PjGrammar.numch b = false).
    { rewrite (exnb_numch_split b Hb8). replace (b - 58) with (b + -58) by lia.
      replace (b - 43) with (b + -43) by lia. rewrite Hd, Hc. reflexivity. }
    exw_run_to RUNTO HS HJ SHOK (exv_pc EXN_CS).
    { exnb_awr. }
    exnb_mem HF Hm.
    lazymatch goal with HS : st_ok _ ?E' ?ss (restrict _ ?ms) |- _ =>
      apply (exnb_close_stop fxc lyc Sc Hpl Wc regs memc mdc k c j [Z_to_bv 64 b] E' ss ms _ HPRE HCL HS
        ltac:(vm_compute; reflexivity) ltac:(rewrite <- HE; apply exw_agree2) Hm HJ
        ltac:(rewrite Hbeq; exact Hn))
    end.
  + (* in the range: the mask bit *)
    rename Hc into Hr.
    exw_run RUN HS HJ SHOK.
    { exnb_awr. }
    exnb_mem HF Hm.
    exw_branch HS SHOK;
      rewrite branch_eq_U in Hc;
      rewrite (exnb_mask_U _ b) in Hc by first [exw_ew E32 | lia | rewrite exn_MASK_value; reflexivity];
      rewrite U_lit in Hc by lia.
    * (* the bit is clear: stop at j *)
      destruct (Z.testbit exn_MASK ((b - 43) mod exn_M64 mod 64)) eqn:Tb; [cbn in Hc; discriminate Hc|].
      assert (Hn : PjGrammar.numch b = false).
      { rewrite (exnb_numch_split b Hb8). replace (b - 58) with (b + -58) by lia.
        replace (b - 43) with (b + -43) in * by lia. rewrite Hd, Hr, Tb. reflexivity. }
      exw_run_to RUNTO HS HJ SHOK (exv_pc EXN_CS).
      { exnb_awr. }
      exnb_mem HF Hm.
      lazymatch goal with HS : st_ok _ ?E' ?ss (restrict _ ?ms) |- _ =>
        apply (exnb_close_stop fxc lyc Sc Hpl Wc regs memc mdc k c j [Z_to_bv 64 b] E' ss ms _ HPRE HCL HS
          ltac:(vm_compute; reflexivity) ltac:(rewrite <- HE; apply exw_agree2) Hm HJ
          ltac:(rewrite Hbeq; exact Hn))
      end.
    * (* the bit is set ('+' '-' '.' 'E' 'e'): 0x83880 and the back edge *)
      destruct (Z.testbit exn_MASK ((b - 43) mod exn_M64 mod 64)) eqn:Tb; [|cbn in Hc; discriminate Hc].
      assert (Hn : PjGrammar.numch b = true).
      { rewrite (exnb_numch_split b Hb8). replace (b - 58) with (b + -58) by lia.
        replace (b - 43) with (b + -43) in * by lia. rewrite Hd, Hr, Tb. reflexivity. }
      clear Hc.
      exw_run RUN HS HJ SHOK.
      { exnb_awr. }
      exnb_mem HF Hm.
      exw_branch HS SHOK;
        rewrite branch_ne_U, !U_SOff in Hc; cbn [ew ewset Nat.eqb] in Hc; rewrite E22, E12 in Hc;
        rewrite !unsigned_lit_small in Hc by lia; rewrite !zcanon_id in Hc by (unfold M64; lia).
      -- apply negb_true_iff, Z.eqb_neq in Hc.
         exw_run_to RUNTO HS HJ SHOK (exv_pc EXN_CL).
         { exnb_awr. }
         exnb_mem HF Hm.
         lazymatch goal with HS : st_ok _ ?E' ?ss (restrict _ ?ms) |- _ =>
           apply (exnb_close_loop m fxc lyc Sc Hpl Wc regs memc mdc k c j [Z_to_bv 64 b] E' ss ms _ IH Hmj HPRE HCL HS
             ltac:(vm_compute; reflexivity) ltac:(rewrite <- HE; apply exw_agree2) Hm HJ
             ltac:(rewrite Hbeq; exact Hn) ltac:(lia))
         end.
      -- apply negb_false_iff, Z.eqb_eq in Hc.
         exw_run_to RUNTO HS HJ SHOK (exv_pc EXN_CS).
         { exnb_awr. }
         exnb_mem HF Hm.
         lazymatch goal with HS : st_ok _ ?E' ?ss (restrict _ ?ms) |- _ =>
           apply (exnb_close_end fxc lyc Sc Hpl Wc regs memc mdc k c j [Z_to_bv 64 b] E' ss ms _ HPRE HCL HS
             ltac:(vm_compute; reflexivity) ltac:(rewrite <- HE; apply exw_agree2) Hm HJ
             ltac:(rewrite Hbeq; exact Hn) ltac:(lia))
         end.
Qed.

Lemma exnb_base0 : exnb_KL 0.
Proof.
intros fxc lyc Sc Hpl Wc regs memc mdc k c j Hmj HPRE HCL. exfalso.
destruct HCL as (_ & _ & _ & _ & _ & Hj & _). lia.
Qed.

Lemma exnb_all : forall m, exnb_KL m.
Proof. induction m as [|m IHm]; [exact exnb_base0 | exact (exnb_step m IHm)]. Qed.

(* sub-piece Bp: CL -> CS (ExvB_NumCut.v EXN_Bl) *)
Lemma exn_Bl : EXN_Bl B ARx SK E pos.
Proof using HYP HC MK KS.
intros fxc lyc Sc Hpl Wc regs memc mdc k c j HPRE HCL.
exact (exnb_all _ fxc lyc Sc Hpl Wc regs memc mdc k c j eq_refl HPRE HCL).
Qed.
End p.
