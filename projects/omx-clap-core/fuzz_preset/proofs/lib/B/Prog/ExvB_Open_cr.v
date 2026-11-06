(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Rebound onto the old-pin kit 4f18c75d4900 (base cold/h-rw-pre-7-b-ex_value-rebind): EXB carries exv_rm, the
   memnorm keep from the entry memory, across every run by ExvB_Loop_exw.v's _inv runners at P := exvl_P (e_mem E)
   and across the ex_ws call by its m-form post. Does not rest on tex_word_specX. *)
(* Theorem Labs, 2026-10: fuzz_preset, image B, ex_value, segment CI, the stretch AFTER ex_ws (CR): B entry + 0x460
   (0x8398c, ex_ws's return site) to the loop head CL (entry + 0x534) or the close CC (entry + 0x9f8).
   - entry + 0x460 .. + 0x478: ASan checks of in->p / in->end (shadow of q, q + 8, through s4 / s6), end := *(q + 8),
     p' := *q, `bgeu p', end` -> loop init (+ 0x4c0);
   - else UBSan p' <> 0, ASan check of the byte at p' (slow path + 0xba8 returns for a partial granule), b := *p',
     s8 := 120(s1) (the frame, unchanged), closer := 64(s1), `bne b, closer` -> loop init;
   - else (b = closer) UBSan p' <> -1, ASan check of q (through a3 = s4), in->p := p' + 1, `j` CC with a1 = 0;
   - loop init (+ 0x4c0 .. + 0x530): 128 / 112 / 136(s1) := 0, the vv- and q-derived spills, 8(s1) := 3, 32(s1) :=
     2 ^ 60, then CL.
   The symbolic engine is the table engine over B's whole-range listing (YCbqG SRr_run_tok_AJx / SRr_run_to_tok_AJx,
   B_prog_tbl; their _inv twins of ExvB_Loop_exw.v), the idioms of lib/B/Prog/ExvB_Open_f1.v and of
   lib/B/Prog/ex_ws_x.v (restated in ExvB_Loop_exw.v). The case split is on the cursor
   after ex_ws, skipn ip x = skip (skipn (S i1) x) (ExvB_Open_pure.v exv_ip_skip): [] (p' = end: CL by exv_V_loop) or
   c' :: r (p' < end, the byte c' read at p': CC by exv_V_close if c' is the closer, else CL by exv_V_loop). Every
   error site of the stretch is shown unreachable inside exo_cr's runs (the engine takes only the not-taken arm):
   ASan reports B 0x8421c (guard 0x83990, shadow of q) and 0x84224 (guard 0x83998, shadow of q + 8) by the shadow entry
   of q's 40 bytes (EXB's range_addressable, run 1 of both cases); 0x840dc (guard 0x839bc, slow path 0x840d4) by the
   shadow entry of the byte at p' (EXB's src_rd, run 2 of the case c' :: r); 0x8422c (guard 0x839dc, through a3) by
   q's entry (the CC arm, after the re-pin); the UBSan trap 0x8407c from its guards 0x839a8 (p' = 0) and 0x839d4
   (p' = -1) by the fact p' in [4096, 2 ^ 47 - 2] (exo_PF). Engine stops measured on f8f98a95 (scratch probe):
   + 0x478 SR_branch BC_GEU (SOff 34 0) (SOff 35 0); + 0x4a0 SR_branch BC_NE (SOff 36 0) (SOff 32 0); + 0x4ac SR_addr
   (a3 = s4 + 0, the `mv`: the register is re-pinned to s4's shadow term, exr_st_ok_set_reg / exr_add0, and the run
   continues to CC with a1 = SLit 0).
   Rule 24: proves no function (kind: segment lemma). Numerals: 0x460, 0x534, 0x9f8 (DERIVED: cut offsets, B entry +
   offset from the internal file neutral_dis.py on the record f8f98a95bc52); 2, 3, 4, 8, 9, 11, 13, 18-27 (WORD: register numbers); 32-36
   (DERIVED: the engine's extra atoms); 8, 16, 24, 32, 40, 48, 56, 64, 72, 80, 88, 96, 104, 112, 120, 128, 136, 144,
   152, 160, 176 (LENGTH: slot offsets of B's code); 0, 8, 16, 20, 24, 32, 36, 40 (LENGTH: struct ex fields); 3
   (DERIVED: (q + 32) & 7 + 3 at q 8-aligned); 2 ^ 60 (WORD: the code's mask constant); 91, 93, 123, 125 (WORD: ASCII);
   255, 256 (LENGTH: byte range); 4096, 2 ^ 32, 2 ^ 46, 2 ^ 47, 2 ^ 63, 2 ^ 64, 17592186044416 (LENGTH: bounds; 2 ^ 44,
   the shadow band); 0x7fff8000 (DERIVED: SHADOW_OFF). No ADDRESS. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YImgTop YC1fP YCbqG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames FCiface YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_FnEx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_Reader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Img0 Listing_prog PAImg_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import ExvB_Loop_exw.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import
ExvB_Stmt ExvB_Open_pure ExvB_Open_kt ExvB_Open_fin ExvB_Open_f1.
Import ListNotations.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

#[local] Existing Instance prh_img_B.

(* ---- the stretch's symbolic states: atoms 32 closer, 33 vv, 34 p' (= x0 + ip), 35 end (= x0 + len), 36 the byte ---- *)
Definition EXR_CR : Z := exv_pc 0x460.
Definition EXR_CL : Z := exv_pc 0x534.
Definition EXR_CC : Z := exv_pc 0x9f8.
Definition exr_regs : list sv :=
  sr_set (sr_set (sr_set sr_atoms 20%bv (exo_shx (SOff 19 0))) 22%bv (exo_shx (SOff 19 8))) 23%bv (SOff 19 8).
Definition exr_fr : YP09.region :=
  YP09.mkRegion (Some 9%nat) 8 160 8 160
    [YP09.mkChunk 64 (CVal 8 (SOff 32 0)); YP09.mkChunk 96 (CVal 8 (SOff 19 16));
     YP09.mkChunk 104 (CVal 8 (exo_shx (SOff 19 16))); YP09.mkChunk 120 (CVal 8 (SOff 24 0));
     YP09.mkChunk 144 (CVal 8 (exo_shx (SOff 19 0))); YP09.mkChunk 152 (CVal 8 (SOff 33 0))].
Definition exr_rq : YP09.region :=
  YP09.mkRegion (Some 19%nat) 0 16 0 8 [YP09.mkChunk 0 (CVal 8 (SOff 34 0)); YP09.mkChunk 8 (CVal 8 (SOff 35 0))].
Definition exr_rb : YP09.region := YP09.mkRegion (Some 34%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 36 0))].
Definition exr_fcA : list (nat * afact) :=
[ (9%nat, exo_SPF); (19%nat, exo_QF); (25%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (27%nat, mkAF 91 123 0);
  (34%nat, exo_PF) ].
Definition exr_fcB : list (nat * afact) :=
[ (9%nat, exo_SPF); (19%nat, exo_QF); (25%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (27%nat, mkAF 91 123 0);
  (34%nat, exo_PF); (36%nat, mkAF 0 255 0) ].
Definition ss_crA : sstate := mkSS EXR_CR exr_regs [exr_fr; exr_rq] None (mkFacts exr_fcA [] []).
Definition ss_crB : sstate := mkSS EXR_CR exr_regs [exr_fr; exr_rq; exr_rb] None (mkFacts exr_fcB [] []).
Definition exr_SHA : list shent := [mkSHE 19 0 40].
Definition exr_SHB : list shent := [mkSHE 19 0 40; mkSHE 34 0 1].

(* ---- pure helpers ---- *)
Lemma exr_add0 : forall E e, sv_denot E (SAlu ALU_ADD e (SLit 0)) = sv_denot E e.
Proof.
intros E e. apply bv_eq. change (U E (SAlu ALU_ADD e (SLit 0)) = U E e).
rewrite U_SAlu, U_SLit. cbn [zalu_raw]. rewrite (zcanon_id 0) by (unfold M64; lia). rewrite Z.add_0_r.
apply zcanon_id. apply U_range.
Qed.

(* rewrite the shadow term exo_shx (SOff n z) at the goal's own environment (after a run it extends En) *)
Ltac exr_shx_rw n z v E1 E25 :=
  lazymatch goal with |- sv_denot ?EE _ = _ =>
    let H1 := fresh "H1" in let H2 := fresh "H2" in
    assert (H1 : ew EE n = Z_to_bv 64 v) by exw_ew E1;
    assert (H2 : ew EE 25 = Z_to_bv 64 SHADOW_OFF) by exw_ew E25;
    rewrite (exo_denot_shx EE n z v SHADOW_OFF H1 H2) by (unfold SHADOW_OFF; lia);
    clear H1 H2
  end.

Section r. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world rsegs -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
Hypothesis HYP : EXV_HYP B ARx SK.
Let LAWS := eh_laws B ARx SK HYP.
Let RUN (mem0 : word -> option byte) := SRr_run_tok_AJx_inv (SK := SK) rsegs B (@prh_pst prh_img_B) ARx LAWS
  B_prog_segs_low B_prog_tbl B_prog_tbl_ok B_prog_wx (exvl_P mem0) (exvl_PLAW mem0).
Let RUNTO (mem0 : word -> option byte) := SRr_run_to_tok_AJx_inv (SK := SK) rsegs B (@prh_pst prh_img_B) ARx LAWS
  B_prog_segs_low B_prog_tbl B_prog_tbl_ok B_prog_wx (exvl_P mem0) (exvl_PLAW mem0).

(* a register whose symbolic value is respelled by an equal denotation (YI08.v st_ok_set_reg, restated) *)
Lemma exr_st_ok_set_reg : forall (segs : list Segment) E ss ms (r : bv 5) e,
  st_ok segs E ss ms -> r <> 0%bv -> YK11.getr (ms_regs ms) r = sv_denot E e ->
  st_ok segs E (mkSS (ss_pc ss) (sr_set (ss_regs ss) r e) (ss_mem ss) (ss_resv ss) (ss_facts ss)) ms.
Proof.
intros segs E ss ms r e (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9) Hr He.
unfold st_ok; cbn. repeat (split; [assumption|]). split; [|split; assumption].
apply regs_ok_pin; assumption.
Qed.

(* a stretch from CR writes only [s1 + 8, s1 + 160) and in->p: exv_kt's keep premise, and the cursor's other cells *)
Lemma exr_keep : forall E (Wc : world rsegs) memc memc',
  EXV_PRE B ARx E ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ ((exv_s1 E + 8 <= a < exv_s1 E + 160) \/ (e_q E <= a < e_q E + 8)) ->
     aview rsegs (w_H Wc) memc' a = aview rsegs (w_H Wc) memc a) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (exv_sp E - exv_STK E <= a < exv_s1 E + 176) ->
     ~ (inFP (exv_FP E) a /\ e_q E <= a < e_q E + 40) ->
     aview rsegs (w_H Wc) memc' a = aview rsegs (w_H Wc) memc a) /\
  (forall o (n : nat) v, 8 <= o -> o + Z.of_nat n <= 40 ->
     val_mem rsegs (mrestrict (w_H Wc) memc) (e_q E + o) n v ->
     val_mem rsegs (mrestrict (w_H Wc) memc') (e_q E + o) n v).
Proof.
intros E Wc memc memc' HPRE HK.
pose proof HPRE as HPRE'. unfold EXV_PRE in HPRE'. cbv zeta in HPRE'.
destruct HPRE' as (HFP & _ & _ & _ & _ & _ & _ & _ & Hspq & Hqd & Hwin & _).
destruct HFP as ((_ & _ & _ & _ & _ & Hastk & _) & _).
destruct Hastk as (_ & _ & _ & _ & _ & H47 & _ & _ & Htop).
destruct Hwin as (_ & _ & Hdtop & _).
pose proof (exv_s1_le E) as ((S1a & S1b) & _).
pose proof (exo_STK_ge E) as HSTK.
assert (Hsp0 : 0 <= spZ (e_regs E)) by (pose proof (bv_unsigned_in_range _ (YK11.getr (e_regs E) 2%bv)); unfold spZ; lia).
assert (Hq47 : e_q E + 40 <= 2 ^ 47) by (unfold exv_sp in *; lia).
split.
- apply (exo_kept_T1 E Wc memc memc' 8 160); [unfold exv_sp in *; lia | lia |].
  intros a Ha Hz. apply HK; [exact Ha|]. intros [Hw|Hw]; apply Hz; [left | right; left]; exact Hw.
- intros o n v Ho Hn HV. eapply exk_val_kept; [|exact HV].
  intros x Hx. unfold exv_sp in *. apply HK; [lia|]. lia.
Qed.

(* the CC end: the closer right after the whitespace, in->p = x0 + ip + 1, a1 = 0 *)
Lemma exr_cc_fin : forall n, CUT_CC (fx := fx) B ARx SK n ->
  forall E lyc Sc Hpc (Wc : world rsegs) (regs : bvmap 5 word) memc mdc k pos c vv dlc ip r
    (regs' : bvmap 5 word) memc' mdc',
  e_n E = n -> EXV_PRE B ARx E -> EXB B ARx SK E lyc Sc Hpc Wc regs memc mdc k pos ->
  (c = 91 \/ c = 123) -> e_dep E + 1 <= 32 ->
  prhex_cur Wc memc (e_q E) (e_x0 E + ip) (e_x0 E + exv_len E) (e_dep E + 1) (e_scr E) dlc ->
  (dlc = 0 \/ dlc = 1) -> exv_dif E (c =? 123) vv dlc [] ->
  0 <= ip < exv_len E ->
  exv_V E = Some (PjGrammar.mk (c =? 123) (rev []), r) -> skipn (S (Z.to_nat ip)) (e_x E) = r ->
  ajournal_x (SK := SK) rsegs B prh_pst ARx (exv_STK E + e_d E) (exv_sp E + e_d E) (exv_FP E)
    (e_ly E) (e_S E) (e_Hp E) (e_W E) (e_mem E) (e_md E) [(1, pos)] lyc Sc Hpc Wc memc' mdc' k ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ ((exv_s1 E + 8 <= a < exv_s1 E + 160) \/ (e_q E <= a < e_q E + 8)) ->
     aview rsegs (w_H Wc) memc' a = aview rsegs (w_H Wc) memc a) ->
  (forall a, apresent (w_H Wc) memc a -> apresent (w_H Wc) memc' a) ->
  (YAkMemnorm.memnorm rsegs (e_mem E) -> YAkMemnorm.memnorm rsegs memc') ->
  (forall r, In r [2; 3; 4; 8; 9; 18; 19; 24; 25; 26]%bv -> YK11.getr regs' r = YK11.getr regs r) ->
  YK11.getr regs' 11 = w64 0 ->
  val_mem rsegs (mrestrict (w_H Wc) memc') (e_q E) 8 (e_x0 E + ip + 1) ->
  exv_spill E Wc memc' 152 vv -> exv_spill E Wc memc' 96 (e_q E + 16) ->
  exv_spill E Wc memc' 104 (shadow_addr (e_q E + 16)) ->
  SRr rsegs Wc (cfg_at (fx := fx) rsegs (exv_pc 0x9f8) regs' memc' mdc') (EXV_POST B ARx SK E).
Proof.
intros n HC E lyc Sc Hpc Wc regs memc mdc k pos c vv dlc ip r regs' memc' mdc' Hn HPRE HB Hc Hd Hcur Hdlc Hdif
  Hip HV Hr HJ' HK HG HMN HR R11 V0 S152 S96 S104.
destruct (exr_keep E Wc memc memc' HPRE HK) as (HKT & HKV).
destruct Hcur as (_ & C8 & C16 & C24 & C32).
apply (HC E lyc Sc Hpc Wc regs' memc' mdc' k pos c [] (ip + 1) vv dlc Hn HPRE).
- exact (exv_kt B ARx SK HYP E lyc Sc Hpc Wc regs memc mdc k pos regs' memc' mdc' k HPRE HB HJ' HKT HG HMN HR).
- exact Hc.
- exact Hd.
- split; [replace (e_x0 E + (ip + 1)) with (e_x0 E + ip + 1) by lia; exact V0|].
  split; [exact (HKV 8 8%nat _ ltac:(lia) ltac:(cbn; lia) C8)|].
  split; [exact (HKV 16 4%nat _ ltac:(lia) ltac:(cbn; lia) C16)|].
  split; [exact (HKV 24 8%nat _ ltac:(lia) ltac:(cbn; lia) C24)|].
  exact (HKV 32 4%nat _ ltac:(lia) ltac:(cbn; lia) C32).
- lia.
- exact Hdlc.
- rewrite HV. replace (Z.to_nat (ip + 1)) with (S (Z.to_nat ip)) by lia. rewrite Hr. reflexivity.
- exact Hdif.
- exact R11.
- exact S152.
- exact S96.
- exact S104.
Qed.

(* the CL end: the items loop from the empty list at the cursor ip, the loop-init spills of B 0x839ec .. 0x83a5c *)
Lemma exr_cl_fin : forall n, CUT_CL (fx := fx) B ARx SK n ->
  forall E lyc Sc Hpc (Wc : world rsegs) (regs : bvmap 5 word) memc mdc k pos c vv dlc ip
    (regs' : bvmap 5 word) memc' mdc',
  e_n E = n -> EXV_PRE B ARx E -> EXB B ARx SK E lyc Sc Hpc Wc regs memc mdc k pos ->
  exv_i1 E < exv_len E -> nth (Z.to_nat (exv_i1 E)) (e_x E) 0 = c -> (c = 91 \/ c = 123) ->
  e_dep E + 1 <= 32 ->
  prhex_cur Wc memc (e_q E) (e_x0 E + ip) (e_x0 E + exv_len E) (e_dep E + 1) (e_scr E) dlc ->
  (dlc = 0 \/ dlc = 1) -> exv_dif E (c =? 123) vv dlc [] ->
  0 <= ip <= exv_len E ->
  exv_V E = exv_L (S (Z.to_nat (e_dep E))) (c =? 123) 0 0 [] (skipn (Z.to_nat ip) (e_x E)) ->
  ajournal_x (SK := SK) rsegs B prh_pst ARx (exv_STK E + e_d E) (exv_sp E + e_d E) (exv_FP E)
    (e_ly E) (e_S E) (e_Hp E) (e_W E) (e_mem E) (e_md E) [(1, pos)] lyc Sc Hpc Wc memc' mdc' k ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ ((exv_s1 E + 8 <= a < exv_s1 E + 160) \/ (e_q E <= a < e_q E + 8)) ->
     aview rsegs (w_H Wc) memc' a = aview rsegs (w_H Wc) memc a) ->
  (forall a, apresent (w_H Wc) memc a -> apresent (w_H Wc) memc' a) ->
  (YAkMemnorm.memnorm rsegs (e_mem E) -> YAkMemnorm.memnorm rsegs memc') ->
  (forall r, In r [2; 3; 4; 8; 9; 18; 19; 24; 25; 26; 27]%bv -> YK11.getr regs' r = YK11.getr regs r) ->
  YK11.getr regs 27 = w64 c ->
  YK11.getr regs' 22 = w64 (shadow_addr (e_q E + 8)) -> YK11.getr regs' 23 = w64 (e_q E + 8) ->
  val_mem rsegs (mrestrict (w_H Wc) memc') (e_q E) 8 (e_x0 E + ip) ->
  exv_spill E Wc memc' 152 vv -> exv_spill E Wc memc' 88 (vv + 40) -> exv_spill E Wc memc' 56 (vv + 24) ->
  exv_spill E Wc memc' 48 (vv + 32) -> exv_spill E Wc memc' 40 (shadow_addr (vv + 32)) ->
  exv_spill E Wc memc' 80 (e_q E + 32) -> exv_spill E Wc memc' 24 (e_q E + 24) ->
  exv_spill E Wc memc' 16 (shadow_addr (e_q E + 24)) -> exv_spill E Wc memc' 72 (shadow_addr (e_q E + 32)) ->
  exv_spill E Wc memc' 8 3 -> exv_spill E Wc memc' 32 (2 ^ 60) ->
  exv_spill E Wc memc' 136 0 -> exv_spill E Wc memc' 112 0 -> exv_spill E Wc memc' 128 0 ->
  exv_spill E Wc memc' 64 (if c =? 123 then 125 else 93) ->
  exv_spill E Wc memc' 104 (shadow_addr (e_q E + 16)) -> exv_spill E Wc memc' 96 (e_q E + 16) ->
  exv_spill E Wc memc' 120 (frame_addr lyc 1 pos) -> exv_spill E Wc memc' 144 (shadow_addr (e_q E)) ->
  SRr rsegs Wc (cfg_at (fx := fx) rsegs (exv_pc 0x534) regs' memc' mdc') (EXV_POST B ARx SK E).
Proof.
intros n HL E lyc Sc Hpc Wc regs memc mdc k pos c vv dlc ip regs' memc' mdc' Hn HPRE HB Hi1 Hnth Hc Hd Hcur Hdlc
  Hdif Hip HV HJ' HK HG HMN HR R27 R22 R23 V0 S152 S88 S56 S48 S40 S80 S24 S16 S72 S8 S32 S136 S112 S128 S64 S104 S96
  S120 S144.
destruct (exr_keep E Wc memc memc' HPRE HK) as (HKT & HKV).
destruct Hcur as (_ & C8 & C16 & C24 & C32).
apply (HL E lyc Sc Hpc Wc regs' memc' mdc' k pos c 0%nat 0%nat [] ip vv dlc Hn HPRE).
- apply (exv_kt B ARx SK HYP E lyc Sc Hpc Wc regs memc mdc k pos regs' memc' mdc' k HPRE HB HJ' HKT HG HMN).
  intros r Hr. apply HR. cbn [In] in Hr |- *. tauto.
- exact Hi1.
- exact Hnth.
- exact Hc.
- exact Hd.
- reflexivity.
- split; [exact V0|].
  split; [exact (HKV 8 8%nat _ ltac:(lia) ltac:(cbn; lia) C8)|].
  split; [exact (HKV 16 4%nat _ ltac:(lia) ltac:(cbn; lia) C16)|].
  split; [exact (HKV 24 8%nat _ ltac:(lia) ltac:(cbn; lia) C24)|].
  exact (HKV 32 4%nat _ ltac:(lia) ltac:(cbn; lia) C32).
- exact Hip.
- exact Hdlc.
- lia.
- exact HV.
- exact Hdif.
- rewrite (HR 27%bv ltac:(cbn [In]; repeat (first [left; reflexivity | right]))). exact R27.
- exact R22.
- exact R23.
- exact S152.
- exact S88.
- exact S56.
- exact S48.
- exact S40.
- exact S80.
- exact S24.
- exact S16.
- exact S72.
- exact S8.
- exact S32.
- exact S136.
- exact S112.
- exact S128.
- exact S64.
- exact S104.
- exact S96.
- exact S120.
- exact S144.
Qed.

(* ---- the symbolic stretch ---- *)
Lemma exo_cr : forall n, CUT_CC (fx := fx) B ARx SK n -> CUT_CL (fx := fx) B ARx SK n -> CUT_CR (fx := fx) B ARx SK n.
Proof.
intros n HC HL. unfold CUT_CR.
intros Ex lyc Sc Hpc Wc regs memc mdc k pos c vv dlc. cbv zeta.
set (ip := exv_len Ex - Z.of_nat (length (PjGrammar.skip (skipn (S (Z.to_nat (exv_i1 Ex))) (e_x Ex))))).
intros Hn HPRE HB Hi1 Hnth Hcc Hd1 Hcur Hdlc Hdif R27 R20 R22 R23 S64 S96 S104 S120 S144 S152.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (exo_STK_ge Ex) as HSTK.
pose proof (exv_s1_le Ex) as ((S1a & S1b) & S1m).
pose proof HPRE as HPRE'. unfold EXV_PRE in HPRE'. cbv zeta in HPRE'.
destruct HPRE' as (HFP & _ & _ & _ & _ & _ & Hq8 & _ & Hspq & Hqd & Hwin & _ & _ & Hlen3 & Hi0 & Hdep & _ & Hdl &
  _ & _ & _ & Hsq & Hv & _).
destruct HFP as ((_ & _ & _ & _ & _ & Hastk & _) & _ & Hm64).
destruct Hastk as (Hal & Hstk0 & Hceil & Hslo & Hshi & H47 & _ & _ & Htop).
destruct Hwin as (Hd0 & Hd16 & Hdtop & _).
pose proof HB as (HJ & _ & _ & _ & HHp & _ & HRM0 & HLED & _ & R2 & R8 & R9 & R18 & R24 & R25 & R26 & R19 & R3 & R4 &
  _ & _ & _ & HSRC & _ & _ & _ & HQR & HTREE).
pose proof (proj2 HRM0) as HPM.
pose proof HJ as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
destruct Hly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ehi & _).
pose proof Hcur as (V0 & V8 & V16 & V24 & V32).
pose proof HSRC as (HGT & Hx4 & Hxc & Hxam & Hxra & _).
assert (Hfr : 4096 <= frame_addr lyc 1 pos /\ frame_addr lyc 1 pos + 128 <= alloc_ceiling).
{ pose proof HJ as (HARn & _ & _ & _ & _ & Hfrs & _).
  assert (Hin1 : In (1, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
  destruct (frames_bounds_x rsegs B ARx LAWS _ _ _ _ _ _ 1 pos HARn Hin1) as (F1 & F2 & _).
  change (fs_frame_bytes 1) with 128 in F2. lia. }
(* the grammar: the cursor after ex_ws *)
assert (HX := exv_skipX Ex c Hi0 Hi1 Hnth).
assert (Hsk : skipn (Z.to_nat ip) (e_x Ex) = PjGrammar.skip (skipn (S (Z.to_nat (exv_i1 Ex))) (e_x Ex)))
  by exact (proj1 (exv_ip_skip (e_x Ex) (S (Z.to_nat (exv_i1 Ex))))).
assert (Hipb : 0 <= ip <= exv_len Ex) by exact (proj2 (exv_ip_skip (e_x Ex) (S (Z.to_nat (exv_i1 Ex))))).
assert (Hlen_def : exv_len Ex = Z.of_nat (length (e_x Ex))) by reflexivity.
assert (Hi1' : 0 <= exv_i1 Ex).
{ unfold exv_i1, exv_len, exv_X. pose proof (PjGrammar.skip_len (skipn (Z.to_nat (e_i0 Ex)) (e_x Ex))).
  pose proof (length_skipn (Z.to_nat (e_i0 Ex)) (e_x Ex)). lia. }
unfold exv_sp, exv_STK in *.
set (q := e_q Ex) in *. set (s1 := exv_s1 Ex) in *. set (x0 := e_x0 Ex) in *.
set (cl := if c =? 123 then 125 else 93) in *.
set (b := nth (Z.to_nat ip) (e_x Ex) 0).
assert (Hsp0 : 0 <= spZ (e_regs Ex)) by (pose proof (bv_unsigned_in_range _ (YK11.getr (e_regs Ex) 2%bv)); unfold spZ; lia).
assert (Hcl : 93 <= cl <= 125) by (unfold cl; destruct (c =? 123); lia).
assert (Hc' : 91 <= c <= 123) by (destruct Hcc as [-> | ->]; lia).
assert (Hb : 0 <= b < 256).
{ destruct (Z_lt_le_dec ip (exv_len Ex)) as [Hl|Hl].
  - destruct (HGT (Z.to_nat ip) ltac:(lia)) as [_ Hb]. exact Hb.
  - unfold b. rewrite nth_overflow by lia. lia. }
assert (Hvv : 0 <= vv /\ vv + 56 <= 2 ^ 47).
{ destruct Hdif as [(Hvv0 & _) | (Hvv0 & Hvn & _)]; [rewrite Hvv0; lia|].
  destruct HTREE as [Hv0 | (Hnd & Hhome & _)]; [exfalso; apply Hvn; rewrite Hvv0; exact Hv0|].
  pose proof (exv_foot_rng B ARx SK HYP lyc Sc Hpc Wc memc mdc (e_Lam Ex) (e_peak Ex) (e_cnt Ex) (e_fail Ex)
    (e_ran Ex) (e_most Ex) (e_own Ex) regs (e_v Ex) (e_t Ex) (e_D Ex) HAR HLED Hnd Hhome ltac:(lia)) as FOOT.
  pose proof (FOOT (e_v Ex) ltac:(left; lia)). pose proof (FOOT (e_v Ex + 55) ltac:(left; lia)). lia. }
(* the environment *)
remember (Ereg regs (map (Z_to_bv 64) [cl; vv; x0 + ip; x0 + exv_len Ex; b])) as En eqn:HE.
assert (E9 : ew En 9 = YK11.getr regs 9) by (subst En; exact (ew_Ereg_nat regs _ 9 9%bv eq_refl)).
assert (E19 : ew En 19 = Z_to_bv 64 q) by (subst En; rewrite (ew_Ereg_nat regs _ 19 19%bv eq_refl); exact R19).
assert (E24 : ew En 24 = Z_to_bv 64 (frame_addr lyc 1 pos)) by (subst En; rewrite (ew_Ereg_nat regs _ 24 24%bv eq_refl); exact R24).
assert (E25 : ew En 25 = Z_to_bv 64 SHADOW_OFF) by (subst En; rewrite (ew_Ereg_nat regs _ 25 25%bv eq_refl); exact R25).
assert (E27 : ew En 27 = Z_to_bv 64 c) by (subst En; rewrite (ew_Ereg_nat regs _ 27 27%bv eq_refl); exact R27).
assert (E32 : ew En 32 = Z_to_bv 64 cl) by (subst En; exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew En 33 = Z_to_bv 64 vv) by (subst En; exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew En 34 = Z_to_bv 64 (x0 + ip)) by (subst En; exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew En 35 = Z_to_bv 64 (x0 + exv_len Ex)) by (subst En; exact (ew_Ereg_extra regs _ 3)).
assert (E36 : ew En 36 = Z_to_bv 64 b) by (subst En; exact (ew_Ereg_extra regs _ 4)).
assert (Usp : bv_unsigned (ew En 9) = s1) by (rewrite E9, R9; apply unsigned_lit_small; lia).
assert (Uq : bv_unsigned (ew En 19) = q) by (rewrite E19; apply unsigned_lit_small; lia).
assert (Usb : bv_unsigned (ew En 25) = SHADOW_OFF) by (rewrite E25; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (Uc : bv_unsigned (ew En 27) = c) by (rewrite E27; apply unsigned_lit_small; lia).
assert (Ucl : bv_unsigned (ew En 32) = cl) by (rewrite E32; apply unsigned_lit_small; lia).
assert (Uvv : bv_unsigned (ew En 33) = vv) by (rewrite E33; apply unsigned_lit_small; lia).
assert (Up : bv_unsigned (ew En 34) = x0 + ip) by (rewrite E34; apply unsigned_lit_small; lia).
assert (Ue : bv_unsigned (ew En 35) = x0 + exv_len Ex) by (rewrite E35; apply unsigned_lit_small; lia).
assert (Ub : bv_unsigned (ew En 36) = b) by (rewrite E36; apply unsigned_lit_small; lia).
assert (Dq0 : sv_denot En (exo_shx (SOff 19 0)) = Z_to_bv 64 (SHADOW_OFF + q / 8)).
{ rewrite (exo_denot_shx En 19 0 q SHADOW_OFF E19 E25) by (unfold SHADOW_OFF; lia). f_equal. lia. }
assert (Dq8 : sv_denot En (exo_shx (SOff 19 8)) = Z_to_bv 64 (SHADOW_OFF + (q + 8) / 8))
  by (rewrite (exo_denot_shx En 19 8 q SHADOW_OFF E19 E25) by (unfold SHADOW_OFF; lia); reflexivity).
assert (Dq16 : sv_denot En (exo_shx (SOff 19 16)) = Z_to_bv 64 (SHADOW_OFF + (q + 16) / 8))
  by (rewrite (exo_denot_shx En 19 16 q SHADOW_OFF E19 E25) by (unfold SHADOW_OFF; lia); reflexivity).
(* the parts of the symbolic state at CR common to both cases *)
assert (RGok : regs_ok En exr_regs regs).
{ unfold exr_regs. apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [rewrite HE; apply regs_ok_Ereg | |] | |] | |];
    try (intros X; discriminate X).
  + rewrite Dq0. exact R20.
  + rewrite Dq8. exact R22.
  + cbn [sv_denot]. rewrite Uq. exact R23. }
assert (RFok : region_ok rsegs En (mrestrict (w_H Wc) memc) exr_fr).
{ unfold region_ok, exr_fr.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite Usp. split; [lia|]. split; [lia|].
  split; [intros o Ho; apply (apresent_writable rsegs); apply Hpres; lia|].
  constructor; [|constructor; [|constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]]]].
  - apply (chunk_ok_val rsegs En _ s1 64 8 (SOff 32 0) cl);
      [cbn [sv_denot]; rewrite Ucl, Z.add_0_r; reflexivity | cbn; lia | zside | exact S64].
  - apply (chunk_ok_val rsegs En _ s1 96 8 (SOff 19 16) (q + 16));
      [cbn [sv_denot]; rewrite Uq; reflexivity | cbn; lia | zside | exact S96].
  - apply (chunk_ok_val rsegs En _ s1 104 8 (exo_shx (SOff 19 16)) (shadow_addr (q + 16)));
      [rewrite Dq16; reflexivity | unfold shadow_addr, SHADOW_OFF; cbn; lia | zside | exact S104].
  - apply (chunk_ok_val rsegs En _ s1 120 8 (SOff 24 0) (frame_addr lyc 1 pos));
      [cbn [sv_denot]; rewrite E24, unsigned_lit_small, Z.add_0_r by lia; reflexivity | cbn; lia | zside | exact S120].
  - apply (chunk_ok_val rsegs En _ s1 144 8 (exo_shx (SOff 19 0)) (shadow_addr q));
      [rewrite Dq0; reflexivity | unfold shadow_addr, SHADOW_OFF; cbn; lia | zside | exact S144].
  - apply (chunk_ok_val rsegs En _ s1 152 8 (SOff 33 0) vv);
      [cbn [sv_denot]; rewrite Uvv, Z.add_0_r; reflexivity | cbn; lia | zside | exact S152]. }
assert (RQok : region_ok rsegs En (mrestrict (w_H Wc) memc) exr_rq).
{ unfold region_ok, exr_rq.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite Uq. split; [lia|]. split; [lia|].
  split; [intros o Ho; apply (apresent_writable rsegs); apply Hpres; lia|].
  constructor; [|constructor; [|constructor]].
  - apply (chunk_ok_val rsegs En _ q 0 8 (SOff 34 0) (x0 + ip));
      [cbn [sv_denot]; rewrite Up, Z.add_0_r; reflexivity | cbn; lia | zside | rewrite Z.add_0_r; exact V0].
  - apply (chunk_ok_val rsegs En _ q 8 8 (SOff 35 0) (x0 + exv_len Ex));
      [cbn [sv_denot]; rewrite Ue, Z.add_0_r; reflexivity | cbn; lia | zside | exact V8]. }
assert (HBx : U En exo_Bx = SHADOW_OFF) by (unfold exo_Bx; rewrite (U_atom En 25 SHADOW_OFF E25) by (unfold SHADOW_OFF; lia); reflexivity).
assert (SHq : shent_ok rsegs exo_Bx En (mrestrict (w_H Wc) memc) (mkSHE 19 0 40)).
{ apply (shent_ok_of_range rsegs (w_H Wc) memc En exo_Bx 19 q 40 q 0 40 HQR HBx);
    [rewrite (U_atom En 19 q E19) by lia; reflexivity | lia | lia |].
  intros x Hx. unfold SHADOW_OFF. lia. }
unfold cfg_at. change (w64 (exv_pc 0x460)) with (Z_to_bv 64 EXR_CR).
destruct (skipn (Z.to_nat ip) (e_x Ex)) as [|c' r] eqn:Hsk'.
- (* ---- the whitespace runs to the end: p' = end, loop init, CL ---- *)
  assert (Hipl : ip = exv_len Ex).
  { pose proof (length_skipn (Z.to_nat ip) (e_x Ex)) as L. rewrite Hsk' in L. cbn [length] in L. lia. }
  assert (HVL : exv_V Ex = exv_L (S (Z.to_nat (e_dep Ex))) (c =? 123) 0 0 [] (skipn (Z.to_nat ip) (e_x Ex))).
  { rewrite Hsk', Hsk. apply (exv_V_loop Ex c _ HX Hcc); [lia | lia |].
    intros c'' r'' Hy. rewrite <- Hsk in Hy. discriminate Hy. }
  assert (HS : st_ok rsegs En ss_crA (restrict (w_H Wc) (YK11.mkst regs (Z_to_bv 64 EXR_CR) memc (YK11.seg_rom rsegs)))).
  { rewrite restrict_mkst_fx. unfold ss_crA. apply exw_st_ok_full.
    - exact RGok.
    - vm_compute. reflexivity.
    - constructor; [exact RFok | constructor; [exact RQok | constructor]].
    - apply pairwise_disjoint_of_extents. unfold exr_fr, exr_rq. cbn [map]. unfold extent_of_region.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite Usp, Uq.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
    - split; [|split; [exact I | exact I]].
      cbn [f_atoms atoms_ok exr_fcA]. unfold afact_ok, exo_SPF, exo_QF, exo_PF. cbn [af_lo af_hi af_al2].
      rewrite Usp, Uq, Usb, Uc, Up. change (2 ^ 5) with 32. change (2 ^ 3) with 8.
      rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SHADOW_OFF. repeat split; lia. }
  assert (SHOK : sh_ok rsegs exo_Bx exr_SHA En (mrestrict (w_H Wc) memc)).
  { unfold exr_SHA. constructor; [exact SHq | constructor]. }
  (* run 1: to the `bgeu p', end` *)
  exw_run (RUN (e_mem Ex)) HS HJ SHOK HPM.
  { exo_awr Usp Uq. }
  exw_kept_of HFr (fun a => (s1 + 8 <= a < s1 + 160) \/ (q <= a < q + 8))
    ltac:(fun h => cbn [ew ewset Nat.eqb] in h; rewrite ?Usp, ?Uq in h).
  rename KEPT into K1. rename HG into G1.
  clear HF HFr.
  exw_branch HS SHOK.
  + (* p' >= end: loop init to CL *)
    exw_run_to (RUNTO (e_mem Ex)) HS HJ SHOK HPM EXR_CL.
    { exo_awr Usp Uq. }
    exw_kept_of HFr (fun a => (s1 + 8 <= a < s1 + 160) \/ (q <= a < q + 8))
      ltac:(fun h => cbn [ew ewset Nat.eqb] in h; rewrite ?Usp, ?Uq in h).
    rename KEPT into K2. rename HG into G2.
    clear HF HFr.
    lazymatch type of HS with st_ok _ ?Ex' _ (restrict _ ?msF) =>
      assert (AG2 : env_agree 32 (Ereg regs (map (Z_to_bv 64) [cl; vv; x0 + ip; x0 + exv_len Ex; b])) Ex')
        by (rewrite <- HE; split; [intros nn Hnn; repeat (rewrite ew_ewset_other by lia); reflexivity | reflexivity]);
      pose proof (regs_kept_of_st_ok rsegs _ _ _ regs _ [2; 3; 4; 8; 9; 18; 19; 24; 25; 26; 27]%bv HS AG2
        ltac:(vm_compute; reflexivity)) as KR
    end.
    pose proof (st_ok_restrict_reg rsegs (w_H Wc) _ _ _ 22%bv HS) as R22'.
    pose proof (st_ok_restrict_reg rsegs (w_H Wc) _ _ _ 23%bv HS) as R23'.
    lazymatch type of R22' with _ = sv_denot ?Ex' (sr_get ?l _) =>
      change (sr_get l 22%bv) with (exo_shx (SOff 19 8)) in R22';
      change (sr_get l 23%bv) with (SOff 19 8) in R23';
      rewrite (exo_denot_shx Ex' 19 8 q SHADOW_OFF ltac:(exw_ew E19) ltac:(exw_ew E25)) in R22' by (unfold SHADOW_OFF; lia)
    end.
    cbn [sv_denot ew ewset Nat.eqb] in R23'. rewrite Uq in R23'. cbn [ms_regs restrict] in R22', R23'.
    pose proof (exw_region_nth rsegs _ _ _ 0 _ HS eq_refl) as RF. cbn [ms_mem restrict] in RF.
    pose proof (exw_region_nth rsegs _ _ _ 1 _ HS eq_refl) as RQ. cbn [ms_mem restrict] in RQ.
    pose proof (exw_field rsegs _ _ 19%nat q _ _ _ _ _ 0 8 (SOff 34 0) (x0 + ip) RQ ltac:(cbn [ew ewset Nat.eqb]; exact Uq)
      ltac:(cbn [In]; repeat (first [left; reflexivity | right]))
      ltac:(cbn [sv_denot ew ewset Nat.eqb]; rewrite Up, Z.add_0_r; reflexivity) ltac:(cbn; lia) ltac:(zside)) as VQ.
    rewrite Z.add_0_r in VQ.
    pose proof (exw_field rsegs _ _ 9%nat s1 _ _ _ _ _ 152 8 (SOff 33 0) vv RF ltac:(cbn [ew ewset Nat.eqb]; exact Usp)
      ltac:(cbn [In]; repeat (first [left; reflexivity | right]))
      ltac:(cbn [sv_denot ew ewset Nat.eqb]; rewrite Uvv, Z.add_0_r; reflexivity) ltac:(cbn; lia) ltac:(zside)) as P152.
    pose proof (exw_field rsegs _ _ 9%nat s1 _ _ _ _ _ 88 8 (SOff 33 40) (vv + 40) RF ltac:(cbn [ew ewset Nat.eqb]; exact Usp)
      ltac:(cbn [In]; repeat (first [left; reflexivity | right]))
      ltac:(cbn [sv_denot ew ewset Nat.eqb]; rewrite Uvv; reflexivity) ltac:(cbn; lia) ltac:(zside)) as P88.
    pose proof (exw_field rsegs _ _ 9%nat s1 _ _ _ _ _ 56 8 (SOff 33 24) (vv + 24) RF ltac:(cbn [ew ewset Nat.eqb]; exact Usp)
      ltac:(cbn [In]; repeat (first [left; reflexivity | right]))
      ltac:(cbn [sv_denot ew ewset Nat.eqb]; rewrite Uvv; reflexivity) ltac:(cbn; lia) ltac:(zside)) as P56.
    pose proof (exw_field rsegs _ _ 9%nat s1 _ _ _ _ _ 48 8 (SOff 33 32) (vv + 32) RF ltac:(cbn [ew ewset Nat.eqb]; exact Usp)
      ltac:(cbn [In]; repeat (first [left; reflexivity | right]))
      ltac:(cbn [sv_denot ew ewset Nat.eqb]; rewrite Uvv; reflexivity) ltac:(cbn; lia) ltac:(zside)) as P48.
    pose proof (exw_field rsegs _ _ 9%nat s1 _ _ _ _ _ 40 8 (exo_shx (SOff 33 32)) (shadow_addr (vv + 32)) RF
      ltac:(cbn [ew ewset Nat.eqb]; exact Usp) ltac:(cbn [In]; repeat (first [left; reflexivity | right]))
      ltac:(exr_shx_rw (33%nat) (32) vv E33 E25; reflexivity)
      ltac:(unfold shadow_addr, SHADOW_OFF; cbn; lia) ltac:(zside)) as P40.
    pose proof (exw_field rsegs _ _ 9%nat s1 _ _ _ _ _ 80 8 (SOff 19 32) (q + 32) RF ltac:(cbn [ew ewset Nat.eqb]; exact Usp)
      ltac:(cbn [In]; repeat (first [left; reflexivity | right]))
      ltac:(cbn [sv_denot ew ewset Nat.eqb]; rewrite Uq; reflexivity) ltac:(cbn; lia) ltac:(zside)) as P80.
    pose proof (exw_field rsegs _ _ 9%nat s1 _ _ _ _ _ 24 8 (SOff 19 24) (q + 24) RF ltac:(cbn [ew ewset Nat.eqb]; exact Usp)
      ltac:(cbn [In]; repeat (first [left; reflexivity | right]))
      ltac:(cbn [sv_denot ew ewset Nat.eqb]; rewrite Uq; reflexivity) ltac:(cbn; lia) ltac:(zside)) as P24.
    pose proof (exw_field rsegs _ _ 9%nat s1 _ _ _ _ _ 16 8 (exo_shx (SOff 19 24)) (shadow_addr (q + 24)) RF
      ltac:(cbn [ew ewset Nat.eqb]; exact Usp) ltac:(cbn [In]; repeat (first [left; reflexivity | right]))
      ltac:(exr_shx_rw (19%nat) (24) q E19 E25; reflexivity)
      ltac:(unfold shadow_addr, SHADOW_OFF; cbn; lia) ltac:(zside)) as P16.
    pose proof (exw_field rsegs _ _ 9%nat s1 _ _ _ _ _ 72 8 (exo_shx (SOff 19 32)) (shadow_addr (q + 32)) RF
      ltac:(cbn [ew ewset Nat.eqb]; exact Usp) ltac:(cbn [In]; repeat (first [left; reflexivity | right]))
      ltac:(exr_shx_rw (19%nat) (32) q E19 E25; reflexivity)
      ltac:(unfold shadow_addr, SHADOW_OFF; cbn; lia) ltac:(zside)) as P72.
    pose proof (exw_field rsegs _ _ 9%nat s1 _ _ _ _ _ 8 8 (SLit 3) 3 RF ltac:(cbn [ew ewset Nat.eqb]; exact Usp)
      ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(reflexivity) ltac:(cbn; lia) ltac:(zside)) as P8.
    pose proof (exw_field rsegs _ _ 9%nat s1 _ _ _ _ _ 32 8 (SLit (2 ^ 60)) (2 ^ 60) RF ltac:(cbn [ew ewset Nat.eqb]; exact Usp)
      ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(reflexivity) ltac:(cbn; lia) ltac:(zside)) as P32.
    pose proof (exw_field rsegs _ _ 9%nat s1 _ _ _ _ _ 136 8 (SLit 0) 0 RF ltac:(cbn [ew ewset Nat.eqb]; exact Usp)
      ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(reflexivity) ltac:(cbn; lia) ltac:(zside)) as P136.
    pose proof (exw_field rsegs _ _ 9%nat s1 _ _ _ _ _ 112 8 (SLit 0) 0 RF ltac:(cbn [ew ewset Nat.eqb]; exact Usp)
      ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(reflexivity) ltac:(cbn; lia) ltac:(zside)) as P112.
    pose proof (exw_field rsegs _ _ 9%nat s1 _ _ _ _ _ 128 8 (SLit 0) 0 RF ltac:(cbn [ew ewset Nat.eqb]; exact Usp)
      ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(reflexivity) ltac:(cbn; lia) ltac:(zside)) as P128.
    pose proof (exw_field rsegs _ _ 9%nat s1 _ _ _ _ _ 64 8 (SOff 32 0) cl RF ltac:(cbn [ew ewset Nat.eqb]; exact Usp)
      ltac:(cbn [In]; repeat (first [left; reflexivity | right]))
      ltac:(cbn [sv_denot ew ewset Nat.eqb]; rewrite Ucl, Z.add_0_r; reflexivity) ltac:(cbn; lia) ltac:(zside)) as P64.
    pose proof (exw_field rsegs _ _ 9%nat s1 _ _ _ _ _ 104 8 (exo_shx (SOff 19 16)) (shadow_addr (q + 16)) RF
      ltac:(cbn [ew ewset Nat.eqb]; exact Usp) ltac:(cbn [In]; repeat (first [left; reflexivity | right]))
      ltac:(exr_shx_rw (19%nat) (16) q E19 E25; reflexivity)
      ltac:(unfold shadow_addr, SHADOW_OFF; cbn; lia) ltac:(zside)) as P104.
    pose proof (exw_field rsegs _ _ 9%nat s1 _ _ _ _ _ 96 8 (SOff 19 16) (q + 16) RF ltac:(cbn [ew ewset Nat.eqb]; exact Usp)
      ltac:(cbn [In]; repeat (first [left; reflexivity | right]))
      ltac:(cbn [sv_denot ew ewset Nat.eqb]; rewrite Uq; reflexivity) ltac:(cbn; lia) ltac:(zside)) as P96.
    pose proof (exw_field rsegs _ _ 9%nat s1 _ _ _ _ _ 120 8 (SOff 24 0) (frame_addr lyc 1 pos) RF
      ltac:(cbn [ew ewset Nat.eqb]; exact Usp) ltac:(cbn [In]; repeat (first [left; reflexivity | right]))
      ltac:(cbn [sv_denot ew ewset Nat.eqb]; rewrite E24, unsigned_lit_small, Z.add_0_r by lia; reflexivity)
      ltac:(cbn; lia) ltac:(zside)) as P120.
    pose proof (exw_field rsegs _ _ 9%nat s1 _ _ _ _ _ 144 8 (exo_shx (SOff 19 0)) (shadow_addr q) RF
      ltac:(cbn [ew ewset Nat.eqb]; exact Usp) ltac:(cbn [In]; repeat (first [left; reflexivity | right]))
      ltac:(exr_shx_rw (19%nat) (0) q E19 E25;
            unfold shadow_addr; f_equal; f_equal; f_equal; lia)
      ltac:(unfold shadow_addr, SHADOW_OFF; cbn; lia) ltac:(zside)) as P144.
    assert (KALL : forall a, 0 <= a < 2 ^ 64 -> ~ ((exv_s1 Ex + 8 <= a < exv_s1 Ex + 160) \/ (e_q Ex <= a < e_q Ex + 8)) ->
      aview rsegs (w_H Wc) (ms_mem ltac:(lazymatch type of HS with st_ok _ _ _ (restrict _ ?mx) => exact mx end)) a =
      aview rsegs (w_H Wc) memc a)
      by (intros a Ha Hna; rewrite K2, K1 by assumption; reflexivity).
    assert (GALL : forall a, apresent (w_H Wc) memc a ->
      apresent (w_H Wc) (ms_mem ltac:(lazymatch type of HS with st_ok _ _ _ (restrict _ ?mx) => exact mx end)) a)
      by (intros a Ha; apply (apresent_grows _ _ _ a G2), (apresent_grows _ _ _ a G1), Ha).
    pmkst HS.
    unfold exvl_P in HPM.
    eapply (exr_cl_fin n HL Ex lyc Sc Hpc Wc regs memc mdc k pos c vv dlc ip); eassumption.
  + (* p' < end: impossible, p' = end *)
    exfalso. rewrite branch_geu_U, !U_SOff in Hc. cbn [ew ewset Nat.eqb] in Hc.
    rewrite Up, Ue, !Z.add_0_r, !zcanon_id in Hc by (unfold M64; lia).
    destruct (Z.ltb_spec (x0 + ip) (x0 + exv_len Ex)); [lia | discriminate Hc].
- (* ---- a byte c' at p' < end ---- *)
  assert (Hipl : ip < exv_len Ex).
  { pose proof (length_skipn (Z.to_nat ip) (e_x Ex)) as L. rewrite Hsk' in L. cbn [length] in L. lia. }
  assert (Hip2 : 0 <= ip < exv_len Ex) by lia.
  assert (Hbc : b = c') by exact (exw_nth_skipn _ _ _ _ Hsk').
  assert (Hy : PjGrammar.skip (skipn (S (Z.to_nat (exv_i1 Ex))) (e_x Ex)) = c' :: r) by exact (eq_sym Hsk).
  assert (Vb : val_mem rsegs (mrestrict (w_H Wc) memc) (x0 + ip) 1 b).
  { destruct (HGT (Z.to_nat ip) ltac:(lia)) as [V _]. replace (x0 + ip) with (x0 + Z.of_nat (Z.to_nat ip)) by lia. exact V. }
  assert (HS : st_ok rsegs En ss_crB (restrict (w_H Wc) (YK11.mkst regs (Z_to_bv 64 EXR_CR) memc (YK11.seg_rom rsegs)))).
  { rewrite restrict_mkst_fx. unfold ss_crB. apply exw_st_ok_full.
    - exact RGok.
    - vm_compute. reflexivity.
    - constructor; [exact RFok | constructor; [exact RQok | constructor; [|constructor]]].
      unfold region_ok, exr_rb.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite Up. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val rsegs En _ (x0 + ip) 0 1 (SOff 36 0) b);
        [cbn [sv_denot]; rewrite Ub, Z.add_0_r; reflexivity | cbn; lia | zside | rewrite Z.add_0_r; exact Vb].
    - apply pairwise_disjoint_of_extents. unfold exr_fr, exr_rq, exr_rb. cbn [map]. unfold extent_of_region.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite Usp, Uq, Up.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
    - split; [|split; [exact I | exact I]].
      cbn [f_atoms atoms_ok exr_fcB]. unfold afact_ok, exo_SPF, exo_QF, exo_PF. cbn [af_lo af_hi af_al2].
      rewrite Usp, Uq, Usb, Uc, Up, Ub. change (2 ^ 5) with 32. change (2 ^ 3) with 8.
      rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SHADOW_OFF. repeat split; lia. }
  assert (SHOK : sh_ok rsegs exo_Bx exr_SHB En (mrestrict (w_H Wc) memc)).
  { unfold exr_SHB. constructor; [exact SHq | constructor; [|constructor]].
    apply (shent_ok_of_range rsegs (w_H Wc) memc En exo_Bx 34 x0 (Z.of_nat (length (e_x Ex))) (x0 + ip) 0 1 Hxra HBx);
      [rewrite (U_atom En 34 (x0 + ip) E34) by lia; reflexivity | lia | lia |].
    intros x Hx. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hxam. unfold SHADOW_OFF. lia. }
  (* run 1: to the `bgeu p', end` *)
  exw_run (RUN (e_mem Ex)) HS HJ SHOK HPM.
  { exo_awr Usp Uq. }
  exw_kept_of HFr (fun a => (s1 + 8 <= a < s1 + 160) \/ (q <= a < q + 8))
    ltac:(fun h => cbn [ew ewset Nat.eqb] in h; rewrite ?Usp, ?Uq in h).
  rename KEPT into K1. rename HG into G1.
  clear HF HFr.
  exw_branch HS SHOK.
  + (* p' >= end: impossible *)
    exfalso. rewrite branch_geu_U, !U_SOff in Hc. cbn [ew ewset Nat.eqb] in Hc.
    rewrite Up, Ue, !Z.add_0_r, !zcanon_id in Hc by (unfold M64; lia).
    destruct (Z.ltb_spec (x0 + ip) (x0 + exv_len Ex)); [discriminate Hc | lia].
  + (* p' < end: the byte against the closer *)
    clear Hc.
    exw_run (RUN (e_mem Ex)) HS HJ SHOK HPM.
    { exo_awr Usp Uq. }
    exw_kept_of HFr (fun a => (s1 + 8 <= a < s1 + 160) \/ (q <= a < q + 8))
      ltac:(fun h => cbn [ew ewset Nat.eqb] in h; rewrite ?Usp, ?Uq in h).
    rename KEPT into K2. rename HG into G2.
    clear HF HFr.
    exw_branch HS SHOK;
      rewrite branch_ne_U, !U_SOff in Hc; cbn [ew ewset Nat.eqb] in Hc;
      rewrite Ub, Ucl, !Z.add_0_r, !zcanon_id in Hc by (unfold M64; lia).
    * (* b <> closer: loop init to CL *)
      apply Bool.negb_true_iff, Z.eqb_neq in Hc.
      assert (HVL : exv_V Ex = exv_L (S (Z.to_nat (e_dep Ex))) (c =? 123) 0 0 [] (skipn (Z.to_nat ip) (e_x Ex))).
      { rewrite Hsk', Hsk. apply (exv_V_loop Ex c _ HX Hcc); [lia | lia |].
        intros c'' r'' Hy'. rewrite Hy in Hy'. injection Hy' as <- <-. intros Hcl2. apply Hc.
        rewrite Hbc, Hcl2. reflexivity. }
      exw_run_to (RUNTO (e_mem Ex)) HS HJ SHOK HPM EXR_CL.
      { exo_awr Usp Uq. }
      exw_kept_of HFr (fun a => (s1 + 8 <= a < s1 + 160) \/ (q <= a < q + 8))
        ltac:(fun h => cbn [ew ewset Nat.eqb] in h; rewrite ?Usp, ?Uq in h).
      rename KEPT into K3. rename HG into G3.
      clear HF HFr.
      lazymatch type of HS with st_ok _ ?Ex' _ (restrict _ ?msF) =>
        assert (AG3 : env_agree 32 (Ereg regs (map (Z_to_bv 64) [cl; vv; x0 + ip; x0 + exv_len Ex; b])) Ex')
          by (rewrite <- HE; split; [intros nn Hnn; repeat (rewrite ew_ewset_other by lia); reflexivity | reflexivity]);
        pose proof (regs_kept_of_st_ok rsegs _ _ _ regs _ [2; 3; 4; 8; 9; 18; 19; 24; 25; 26; 27]%bv HS AG3
          ltac:(vm_compute; reflexivity)) as KR
      end.
      pose proof (st_ok_restrict_reg rsegs (w_H Wc) _ _ _ 22%bv HS) as R22'.
      pose proof (st_ok_restrict_reg rsegs (w_H Wc) _ _ _ 23%bv HS) as R23'.
      lazymatch type of R22' with _ = sv_denot ?Ex' (sr_get ?l _) =>
        change (sr_get l 22%bv) with (exo_shx (SOff 19 8)) in R22';
        change (sr_get l 23%bv) with (SOff 19 8) in R23';
        rewrite (exo_denot_shx Ex' 19 8 q SHADOW_OFF ltac:(exw_ew E19) ltac:(exw_ew E25)) in R22' by (unfold SHADOW_OFF; lia)
      end.
      cbn [sv_denot ew ewset Nat.eqb] in R23'. rewrite Uq in R23'. cbn [ms_regs restrict] in R22', R23'.
      pose proof (exw_region_nth rsegs _ _ _ 0 _ HS eq_refl) as RF. cbn [ms_mem restrict] in RF.
      pose proof (exw_region_nth rsegs _ _ _ 1 _ HS eq_refl) as RQ. cbn [ms_mem restrict] in RQ.
      pose proof (exw_field rsegs _ _ 19%nat q _ _ _ _ _ 0 8 (SOff 34 0) (x0 + ip) RQ ltac:(cbn [ew ewset Nat.eqb]; exact Uq)
        ltac:(cbn [In]; repeat (first [left; reflexivity | right]))
        ltac:(cbn [sv_denot ew ewset Nat.eqb]; rewrite Up, Z.add_0_r; reflexivity) ltac:(cbn; lia) ltac:(zside)) as VQ.
      rewrite Z.add_0_r in VQ.
      pose proof (exw_field rsegs _ _ 9%nat s1 _ _ _ _ _ 152 8 (SOff 33 0) vv RF ltac:(cbn [ew ewset Nat.eqb]; exact Usp)
        ltac:(cbn [In]; repeat (first [left; reflexivity | right]))
        ltac:(cbn [sv_denot ew ewset Nat.eqb]; rewrite Uvv, Z.add_0_r; reflexivity) ltac:(cbn; lia) ltac:(zside)) as P152.
      pose proof (exw_field rsegs _ _ 9%nat s1 _ _ _ _ _ 88 8 (SOff 33 40) (vv + 40) RF ltac:(cbn [ew ewset Nat.eqb]; exact Usp)
        ltac:(cbn [In]; repeat (first [left; reflexivity | right]))
        ltac:(cbn [sv_denot ew ewset Nat.eqb]; rewrite Uvv; reflexivity) ltac:(cbn; lia) ltac:(zside)) as P88.
      pose proof (exw_field rsegs _ _ 9%nat s1 _ _ _ _ _ 56 8 (SOff 33 24) (vv + 24) RF ltac:(cbn [ew ewset Nat.eqb]; exact Usp)
        ltac:(cbn [In]; repeat (first [left; reflexivity | right]))
        ltac:(cbn [sv_denot ew ewset Nat.eqb]; rewrite Uvv; reflexivity) ltac:(cbn; lia) ltac:(zside)) as P56.
      pose proof (exw_field rsegs _ _ 9%nat s1 _ _ _ _ _ 48 8 (SOff 33 32) (vv + 32) RF ltac:(cbn [ew ewset Nat.eqb]; exact Usp)
        ltac:(cbn [In]; repeat (first [left; reflexivity | right]))
        ltac:(cbn [sv_denot ew ewset Nat.eqb]; rewrite Uvv; reflexivity) ltac:(cbn; lia) ltac:(zside)) as P48.
      pose proof (exw_field rsegs _ _ 9%nat s1 _ _ _ _ _ 40 8 (exo_shx (SOff 33 32)) (shadow_addr (vv + 32)) RF
        ltac:(cbn [ew ewset Nat.eqb]; exact Usp) ltac:(cbn [In]; repeat (first [left; reflexivity | right]))
        ltac:(exr_shx_rw (33%nat) (32) vv E33 E25; reflexivity)
        ltac:(unfold shadow_addr, SHADOW_OFF; cbn; lia) ltac:(zside)) as P40.
      pose proof (exw_field rsegs _ _ 9%nat s1 _ _ _ _ _ 80 8 (SOff 19 32) (q + 32) RF ltac:(cbn [ew ewset Nat.eqb]; exact Usp)
        ltac:(cbn [In]; repeat (first [left; reflexivity | right]))
        ltac:(cbn [sv_denot ew ewset Nat.eqb]; rewrite Uq; reflexivity) ltac:(cbn; lia) ltac:(zside)) as P80.
      pose proof (exw_field rsegs _ _ 9%nat s1 _ _ _ _ _ 24 8 (SOff 19 24) (q + 24) RF ltac:(cbn [ew ewset Nat.eqb]; exact Usp)
        ltac:(cbn [In]; repeat (first [left; reflexivity | right]))
        ltac:(cbn [sv_denot ew ewset Nat.eqb]; rewrite Uq; reflexivity) ltac:(cbn; lia) ltac:(zside)) as P24.
      pose proof (exw_field rsegs _ _ 9%nat s1 _ _ _ _ _ 16 8 (exo_shx (SOff 19 24)) (shadow_addr (q + 24)) RF
        ltac:(cbn [ew ewset Nat.eqb]; exact Usp) ltac:(cbn [In]; repeat (first [left; reflexivity | right]))
        ltac:(exr_shx_rw (19%nat) (24) q E19 E25; reflexivity)
        ltac:(unfold shadow_addr, SHADOW_OFF; cbn; lia) ltac:(zside)) as P16.
      pose proof (exw_field rsegs _ _ 9%nat s1 _ _ _ _ _ 72 8 (exo_shx (SOff 19 32)) (shadow_addr (q + 32)) RF
        ltac:(cbn [ew ewset Nat.eqb]; exact Usp) ltac:(cbn [In]; repeat (first [left; reflexivity | right]))
        ltac:(exr_shx_rw (19%nat) (32) q E19 E25; reflexivity)
        ltac:(unfold shadow_addr, SHADOW_OFF; cbn; lia) ltac:(zside)) as P72.
      pose proof (exw_field rsegs _ _ 9%nat s1 _ _ _ _ _ 8 8 (SLit 3) 3 RF ltac:(cbn [ew ewset Nat.eqb]; exact Usp)
        ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(reflexivity) ltac:(cbn; lia) ltac:(zside)) as P8.
      pose proof (exw_field rsegs _ _ 9%nat s1 _ _ _ _ _ 32 8 (SLit (2 ^ 60)) (2 ^ 60) RF ltac:(cbn [ew ewset Nat.eqb]; exact Usp)
        ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(reflexivity) ltac:(cbn; lia) ltac:(zside)) as P32.
      pose proof (exw_field rsegs _ _ 9%nat s1 _ _ _ _ _ 136 8 (SLit 0) 0 RF ltac:(cbn [ew ewset Nat.eqb]; exact Usp)
        ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(reflexivity) ltac:(cbn; lia) ltac:(zside)) as P136.
      pose proof (exw_field rsegs _ _ 9%nat s1 _ _ _ _ _ 112 8 (SLit 0) 0 RF ltac:(cbn [ew ewset Nat.eqb]; exact Usp)
        ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(reflexivity) ltac:(cbn; lia) ltac:(zside)) as P112.
      pose proof (exw_field rsegs _ _ 9%nat s1 _ _ _ _ _ 128 8 (SLit 0) 0 RF ltac:(cbn [ew ewset Nat.eqb]; exact Usp)
        ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(reflexivity) ltac:(cbn; lia) ltac:(zside)) as P128.
      pose proof (exw_field rsegs _ _ 9%nat s1 _ _ _ _ _ 64 8 (SOff 32 0) cl RF ltac:(cbn [ew ewset Nat.eqb]; exact Usp)
        ltac:(cbn [In]; repeat (first [left; reflexivity | right]))
        ltac:(cbn [sv_denot ew ewset Nat.eqb]; rewrite Ucl, Z.add_0_r; reflexivity) ltac:(cbn; lia) ltac:(zside)) as P64.
      pose proof (exw_field rsegs _ _ 9%nat s1 _ _ _ _ _ 104 8 (exo_shx (SOff 19 16)) (shadow_addr (q + 16)) RF
        ltac:(cbn [ew ewset Nat.eqb]; exact Usp) ltac:(cbn [In]; repeat (first [left; reflexivity | right]))
        ltac:(exr_shx_rw (19%nat) (16) q E19 E25; reflexivity)
        ltac:(unfold shadow_addr, SHADOW_OFF; cbn; lia) ltac:(zside)) as P104.
      pose proof (exw_field rsegs _ _ 9%nat s1 _ _ _ _ _ 96 8 (SOff 19 16) (q + 16) RF ltac:(cbn [ew ewset Nat.eqb]; exact Usp)
        ltac:(cbn [In]; repeat (first [left; reflexivity | right]))
        ltac:(cbn [sv_denot ew ewset Nat.eqb]; rewrite Uq; reflexivity) ltac:(cbn; lia) ltac:(zside)) as P96.
      pose proof (exw_field rsegs _ _ 9%nat s1 _ _ _ _ _ 120 8 (SOff 24 0) (frame_addr lyc 1 pos) RF
        ltac:(cbn [ew ewset Nat.eqb]; exact Usp) ltac:(cbn [In]; repeat (first [left; reflexivity | right]))
        ltac:(cbn [sv_denot ew ewset Nat.eqb]; rewrite E24, unsigned_lit_small, Z.add_0_r by lia; reflexivity)
        ltac:(cbn; lia) ltac:(zside)) as P120.
      pose proof (exw_field rsegs _ _ 9%nat s1 _ _ _ _ _ 144 8 (exo_shx (SOff 19 0)) (shadow_addr q) RF
        ltac:(cbn [ew ewset Nat.eqb]; exact Usp) ltac:(cbn [In]; repeat (first [left; reflexivity | right]))
        ltac:(exr_shx_rw (19%nat) (0) q E19 E25;
              unfold shadow_addr; f_equal; f_equal; f_equal; lia)
        ltac:(unfold shadow_addr, SHADOW_OFF; cbn; lia) ltac:(zside)) as P144.
      assert (KALL : forall a, 0 <= a < 2 ^ 64 -> ~ ((exv_s1 Ex + 8 <= a < exv_s1 Ex + 160) \/ (e_q Ex <= a < e_q Ex + 8)) ->
        aview rsegs (w_H Wc) (ms_mem ltac:(lazymatch type of HS with st_ok _ _ _ (restrict _ ?mx) => exact mx end)) a =
        aview rsegs (w_H Wc) memc a)
        by (intros a Ha Hna; rewrite K3, K2, K1 by assumption; reflexivity).
      assert (GALL : forall a, apresent (w_H Wc) memc a ->
        apresent (w_H Wc) (ms_mem ltac:(lazymatch type of HS with st_ok _ _ _ (restrict _ ?mx) => exact mx end)) a)
        by (intros a Ha; apply (apresent_grows _ _ _ a G3), (apresent_grows _ _ _ a G2), (apresent_grows _ _ _ a G1), Ha).
      pmkst HS.
      unfold exvl_P in HPM.
      eapply (exr_cl_fin n HL Ex lyc Sc Hpc Wc regs memc mdc k pos c vv dlc ip); eassumption.
    * (* b = closer: the empty container, in->p := p' + 1, CC *)
      apply Bool.negb_false_iff, Z.eqb_eq in Hc.
      assert (HVC : exv_V Ex = Some (PjGrammar.mk (c =? 123) (rev []), r)).
      { apply (exv_V_close Ex c _ HX Hcc c' r); [lia | lia | exact Hy |]. rewrite <- Hbc, Hc. reflexivity. }
      assert (Hr : skipn (S (Z.to_nat ip)) (e_x Ex) = r) by exact (exw_skipn_S _ _ _ _ Hsk').
      (* run 3: to the ASan load of q's shadow through a3 (= s4 + 0, B `mv a3, s4`) *)
      exw_run (RUN (e_mem Ex)) HS HJ SHOK HPM.
      { exo_awr Usp Uq. }
      exw_kept_of HFr (fun a => (s1 + 8 <= a < s1 + 160) \/ (q <= a < q + 8))
        ltac:(fun h => cbn [ew ewset Nat.eqb] in h; rewrite ?Usp, ?Uq in h).
      rename KEPT into K3. rename HG into G3.
      clear HF HFr.
      (* a3 respelled as s4's shadow term (same denotation), so the engine resolves the shadow load *)
      lazymatch type of HS with st_ok _ ?Ex' ?ss' ?ms' =>
        assert (R13 : YK11.getr (ms_regs ms') 13%bv = sv_denot Ex' (exo_shx (SOff 19 0)));
        [ rewrite (st_ok_reg rsegs Ex' ss' ms' 13%bv HS);
          let e := eval vm_compute in (sr_get (ss_regs ss') 13%bv) in change (sr_get (ss_regs ss') 13%bv) with e;
          first [apply exr_add0 | reflexivity]
        | pose proof (exr_st_ok_set_reg rsegs Ex' ss' ms' 13%bv (exo_shx (SOff 19 0)) HS
            ltac:(intros X; discriminate X) R13) as HS2 ]
      end.
      clear HS R13. rename HS2 into HS.
      exw_run_to (RUNTO (e_mem Ex)) HS HJ SHOK HPM EXR_CC.
      { exo_awr Usp Uq. }
      exw_kept_of HFr (fun a => (s1 + 8 <= a < s1 + 160) \/ (q <= a < q + 8))
        ltac:(fun h => cbn [ew ewset Nat.eqb] in h; rewrite ?Usp, ?Uq in h).
      rename KEPT into K4. rename HG into G4.
      clear HF HFr.
      lazymatch type of HS with st_ok _ ?Ex' _ (restrict _ ?msF) =>
        assert (AG4 : env_agree 32 (Ereg regs (map (Z_to_bv 64) [cl; vv; x0 + ip; x0 + exv_len Ex; b])) Ex')
          by (rewrite <- HE; split; [intros nn Hnn; repeat (rewrite ew_ewset_other by lia); reflexivity | reflexivity]);
        pose proof (regs_kept_of_st_ok rsegs _ _ _ regs _ [2; 3; 4; 8; 9; 18; 19; 24; 25; 26]%bv HS AG4
          ltac:(vm_compute; reflexivity)) as KR
      end.
      pose proof (st_ok_restrict_reg rsegs (w_H Wc) _ _ _ 11%bv HS) as R11'.
      lazymatch type of R11' with _ = sv_denot ?Ex' (sr_get ?l _) =>
        change (sr_get l 11%bv) with (SLit 0) in R11'
      end.
      cbn [sv_denot ms_regs restrict] in R11'.
      pose proof (exw_region_nth rsegs _ _ _ 0 _ HS eq_refl) as RF. cbn [ms_mem restrict] in RF.
      pose proof (exw_region_nth rsegs _ _ _ 1 _ HS eq_refl) as RQ. cbn [ms_mem restrict] in RQ.
      pose proof (exw_field rsegs _ _ 19%nat q _ _ _ _ _ 0 8 (SOff 34 1) (x0 + ip + 1) RQ ltac:(cbn [ew ewset Nat.eqb]; exact Uq)
        ltac:(cbn [In]; repeat (first [left; reflexivity | right]))
        ltac:(cbn [sv_denot ew ewset Nat.eqb]; rewrite Up; reflexivity) ltac:(cbn; lia) ltac:(zside)) as VQ.
      rewrite Z.add_0_r in VQ.
      pose proof (exw_field rsegs _ _ 9%nat s1 _ _ _ _ _ 152 8 (SOff 33 0) vv RF ltac:(cbn [ew ewset Nat.eqb]; exact Usp)
        ltac:(cbn [In]; repeat (first [left; reflexivity | right]))
        ltac:(cbn [sv_denot ew ewset Nat.eqb]; rewrite Uvv, Z.add_0_r; reflexivity) ltac:(cbn; lia) ltac:(zside)) as P152.
      pose proof (exw_field rsegs _ _ 9%nat s1 _ _ _ _ _ 96 8 (SOff 19 16) (q + 16) RF ltac:(cbn [ew ewset Nat.eqb]; exact Usp)
        ltac:(cbn [In]; repeat (first [left; reflexivity | right]))
        ltac:(cbn [sv_denot ew ewset Nat.eqb]; rewrite Uq; reflexivity) ltac:(cbn; lia) ltac:(zside)) as P96.
      pose proof (exw_field rsegs _ _ 9%nat s1 _ _ _ _ _ 104 8 (exo_shx (SOff 19 16)) (shadow_addr (q + 16)) RF
        ltac:(cbn [ew ewset Nat.eqb]; exact Usp) ltac:(cbn [In]; repeat (first [left; reflexivity | right]))
        ltac:(exr_shx_rw (19%nat) (16) q E19 E25; reflexivity)
        ltac:(unfold shadow_addr, SHADOW_OFF; cbn; lia) ltac:(zside)) as P104.
      assert (KALL : forall a, 0 <= a < 2 ^ 64 -> ~ ((exv_s1 Ex + 8 <= a < exv_s1 Ex + 160) \/ (e_q Ex <= a < e_q Ex + 8)) ->
        aview rsegs (w_H Wc) (ms_mem ltac:(lazymatch type of HS with st_ok _ _ _ (restrict _ ?mx) => exact mx end)) a =
        aview rsegs (w_H Wc) memc a)
        by (intros a Ha Hna; rewrite K4, K3, K2, K1 by assumption; reflexivity).
      assert (GALL : forall a, apresent (w_H Wc) memc a ->
        apresent (w_H Wc) (ms_mem ltac:(lazymatch type of HS with st_ok _ _ _ (restrict _ ?mx) => exact mx end)) a)
        by (intros a Ha; apply (apresent_grows _ _ _ a G4), (apresent_grows _ _ _ a G3), (apresent_grows _ _ _ a G2),
              (apresent_grows _ _ _ a G1), Ha).
      pmkst HS.
      unfold exvl_P in HPM.
      eapply (exr_cc_fin n HC Ex lyc Sc Hpc Wc regs memc mdc k pos c vv dlc ip r); eassumption.
Qed.
End r.

Print Assumptions exo_cr.
