(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Rebound onto the old-pin kit of record (4f18c75d4900, engine 459129c18903) on the ex_value
   rebind base: EXB's room conjunct is exv_rm (room / position from the entry state, memnorm keep from the entry
   memory). This segment makes no call and does not change S. memnorm is carried across each engine run by the
   table-engine _inv runners of the shared lib/B/Prog/ExvB_Loop_exw.v (P := exvl_P (e_mem E), started from EXB's exv_rm
   memory half) and handed to the rebound exv_kt as its memnorm premise. The file does not Require ex_ws_x: its
   journal-free helpers and tactics come from ExvB_Loop_exw.v. Does not rest on tex_word_specX. *)
(* Theorem Labs, 2026-10: fuzz_preset, image B (asan-ubsan, rebuilt pin f8f98a95bc52, unstripped twin 3b5e1a099b53),
   ex_value: the CLOSE segment of the walk, B 0x83f24 (= ex_value + 0x9f8, the cut CUT_CC of lib/B/Prog/ExvB_Stmt.v)
   to B 0x83fa8 (= ex_value + 0xa7c, the cut CUT_CX), which is ex_items' tail
       if (v && n != v->n) in->differs = 1;
       in->depth--;
       return 0;
   (fuzz_preset.c :297-300; the C source is read for the meaning only, no plain lemma is cited).
   Instructions walked (neutral listing, the internal file ex_value.fuzz_preset.asan-ubsan.s:640-668, never a raw disassembly):
     0x83f24 ld a0,152(s1)    the node still compared (vv; 0 = the C NULL)
     0x83f28 ld a3,96(s1)     &in->depth  (= q + 16)
     0x83f2c beqz a0 -> 0x83f68
     0x83f30 addi a0,a0,40 / srli / add s9 / lbu / bnez -> 0x84248 (errpath_load8; NOT taken: zero granule shadow)
     0x83f44 ld a0,0(a0)      v->n
     0x83f48 beq a1,a0 -> 0x83f68                       (a1 = the count read, length acc)
     0x83f4c addi a0,s3,32 / srli / add s9 / lb / bnez -> 0x84158 (partial granule, then errpath_store4; NOT taken)
     0x83f60 li a1,1 / sw a1,0(a0)                      in->differs = 1
     0x83f68 ld a0,104(s1) / lb / bnez -> 0x840e0 (partial granule, then errpath_load4; NOT taken)
     0x83f74 lw a1,0(a3)      in->depth (= dep + 1)
     0x83f78 addiw a0,a1,-1
     0x83f7c bge a0,a1 -> 0x8407c `unimp`               UBSan signed-overflow check, NOT taken (dep < dep + 1)
     0x83f80 ld a1,104(s1) / lb / bnez -> 0x840f4 (partial granule, then errpath_store4; NOT taken)
     0x83f8c li s5,0          the result 0
     0x83f90 sw a0,0(a3)      in->depth = dep
     0x83f94 j 0x83fa8
   The ASan shadow bytes read on the main path are resolved INSIDE the symbolic runs (a load of a shadow byte whose
   8-byte granule a shadow entry covers reads 0, YCbn.v tok_load / covered): the cursor's granules [q + 16, q + 24) and
   [q + 32, q + 40) by EXB's range_addressable of [q, q + 40), the node's granule [v + 40, v + 48) by prhex_tree's
   range_addressable of [v, v + 56). The UBSan check at B 0x83f7c is decided by the run too: in->depth is the atom
   dep + 1 with dep in [0, 32], `addiw` gives dep, and `bge dep, dep + 1` is decided not taken (YP0m.v decide_lts on
   one atom). The only undecided branches are `beqz a0` (vv) and `beq a1, a0` (the count), taken both ways below.
   Structure: exvc_close (the cut, B 0x83f24) -> exvc_cmp (B 0x83f30, v not NULL) -> exvc_tail (B 0x83f68) -> the CX
   cut. Across each run EXB is carried by ExvOpen's exv_kt (lib/B/Prog/ExvB_Open_kt.v, shared): the runs write only the
   FP cursor cells [q + 16, q + 20) and [q + 32, q + 36). The functional part: with v the caller's node (tag 5 / 6),
   the count compare against v->n (the node's +40 word = exv_count t) and exv_dif give
   dl' = 1 <-> dl = 1 \/ (v <> 0 /\ t <> mk o (rev acc)) (exvc_res_eq / exvc_res_ne); with vv = 0, exv_dif's NULL arm
   gives it (v NULL, or ex_items' type check failed: tag t <> tag (mk o _)).
   Rule 24: proves no function (kind: segment lemma). Numerals: 0x9f8, 0xa04, 0xa3c, 0xa7c (DERIVED: cut / branch
   offsets from ex_value's entry, neutral listing addresses minus B 0x8352c); 16, 20, 32, 36, 40, 48, 56, 96, 104,
   112, 152, 160, 128, 288, 320 (LENGTH: struct ex / pj_value field offsets, frame slot offsets of B's code, the
   class-1 frame, the realigned frame base's slack); 1, 3 (WORD: the `li a1,1` stored into in->differs, the `srli` 3);
   5, 6 (WORD: PjTree tags of an array / an object); 9, 10, 11, 13, 19, 21, 25, 32, 33 (WORD: register numbers / atom
   indices); 2 ^ 46, 2 ^ 47, 2 ^ 63, 2 ^ 64, 17592186044416 (DERIVED: address-space and shadow-band bounds). No
   ADDRESS: every pc is exv_pc of a DERIVED offset. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0d YP0c YC80 YPsym YC4aP YImgTop YC1fP YCbqG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YGcfRoomKeep FCiface.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_FnEx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_Reader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Img0 Listing_prog PAImg_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import ExvB_Stmt ExvB_Loop_exw ExvB_Open_kt.
Import ListNotations.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

#[local] Existing Instance prh_img_B.

(* ---- the pcs of the segment (DERIVED offsets of ex_value's entry) ---- *)
Definition EXVC_PC : Z := exv_pc 0x9f8.   (* B 0x83f24, the CC cut *)
Definition EXVC_CMP : Z := exv_pc 0xa04.  (* B 0x83f30, the count compare (v is not NULL) *)
Definition EXVC_DEC : Z := exv_pc 0xa3c.  (* B 0x83f68, in->depth-- *)
Definition EXVC_END : Z := exv_pc 0xa7c.  (* B 0x83fa8, the CX cut *)

(* ---- pure: the node count at +40 decides t = mk o (rev acc) (plain lib/Prog/ex_value_l.v / ex_value_i.v read for
   the shape; restated here, no plain lemma cited) ---- *)
Lemma exvc_tag_mk : forall o acc, PjTree.tag (PjGrammar.mk o acc) = (if o then 6 else 5).
Proof. intros [] acc; reflexivity. Qed.

Lemma exvc_count_mk : forall o acc, exv_count (PjGrammar.mk o acc) = length acc.
Proof. intros [] acc; cbn [PjGrammar.mk exv_count]; [reflexivity | apply length_map]. Qed.

Lemma exvc_pref_mk : forall o acc, exv_pref o acc (PjGrammar.mk o (rev acc)).
Proof.
intros [] acc; cbn [PjGrammar.mk exv_pref]; rewrite ?length_rev, ?length_map, ?length_rev;
  (split; [lia | rewrite ?firstn_all2 by (rewrite ?length_map, ?length_rev; lia); reflexivity]).
Qed.

(* the two arms of the compare: equal counts with the prefix agreeing is equality, different counts is difference *)
Lemma exvc_eq_of_pref : forall o acc t,
  exv_pref o acc t -> exv_count t = length acc -> t = PjGrammar.mk o (rev acc).
Proof.
intros [] acc [| | | | | its | ms] H Hc; cbn [exv_pref] in H; try contradiction;
  cbn [exv_count] in Hc; cbn [PjGrammar.mk].
- destruct H as [Hle Hf]. rewrite <- Hf, <- Hc, firstn_all. reflexivity.
- destruct H as [Hle Hf]. rewrite <- Hf, <- Hc, firstn_all. reflexivity.
Qed.

Lemma exvc_pref_len : forall o acc t, exv_pref o acc t -> (length acc <= exv_count t)%nat.
Proof. intros [] acc [| | | | | its | ms] H; cbn [exv_pref] in H; try contradiction; cbn [exv_count]; tauto. Qed.

(* the node's +40 word (pj_value's n, plain PjStruct) is exv_count of a tag-5 / tag-6 tree; the node is 8-aligned *)
Lemma exvc_node_count : forall m lblk p t D (o : bool), PRH_Reader.pj_nodeR rsegs m lblk p t D ->
  PjTree.tag t = (if o then 6 else 5) ->
  p mod 8 = 0 /\ 0 <= Z.of_nat (exv_count t) < 2 ^ 64 /\ val_mem rsegs m (p + 40) 8 (Z.of_nat (exv_count t)).
Proof.
intros m lblk p t D o H Ht.
destruct t as [| | | txt bits | s | its | ms]; destruct o; cbn [PjTree.tag] in Ht; try discriminate;
  cbn [PRH_Reader.pj_nodeR] in H; destruct H as (_ & _ & num & str & kids & keys & nn & cap & Hh & Hb);
  destruct Hh as ((Hal & _) & _ & _ & _ & _ & _ & (Hn1 & Hn2) & _); cbn [exv_count].
- destruct Hb as (_ & _ & Hnn & _). subst nn. split; [exact Hal | split; [exact Hn1 | exact Hn2]].
- destruct Hb as (_ & Hnn & _). subst nn. split; [exact Hal | split; [exact Hn1 | exact Hn2]].
Qed.

(* the shadow address of q + c, in the shape the symbolic run matches (`srli / add s9`, B 0x83f50-0x83f54) *)
Definition exvc_shx (c : Z) : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff 19 c) (SLit 3)) (SOff 25 0).
Definition EXVC_SB : sv := SOff 25 0.

Lemma exvc_denot_shx : forall E c v sb, ew E 19 = Z_to_bv 64 v -> ew E 25 = Z_to_bv 64 sb ->
  0 <= v -> 0 <= c -> v + c < 2 ^ 63 -> 0 <= sb < 2 ^ 32 ->
  sv_denot E (exvc_shx c) = Z_to_bv 64 (sb + (v + c) / 8).
Proof.
intros E c v sb Hn Hm Hv Hc Hvc Hsb. unfold exvc_shx.
rewrite <- (Z_to_bv_bv_unsigned 64 (sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff 19 c) (SLit 3)) (SOff 25 0)))). f_equal.
change (U E (SAlu ALU_ADD (SAlu ALU_SRL (SOff 19 c) (SLit 3)) (SOff 25 0)) = sb + (v + c) / 8).
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SOff, Hn, Hm.
rewrite !unsigned_lit_small by lia. rewrite !Z.add_0_r.
change (Z.land (U E (SLit 3)) 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
rewrite (zcanon_id (v + c)) by (unfold M64; lia).
pose proof (Z.div_pos (v + c) 8 ltac:(lia) ltac:(lia)).
pose proof (Z.div_lt_upper_bound (v + c) 8 (2 ^ 60) ltac:(lia) ltac:(lia)).
rewrite (zcanon_id ((v + c) / 8)) by (unfold M64; lia). rewrite (zcanon_id sb) by (unfold M64; lia).
rewrite zcanon_id by (unfold M64; lia). lia.
Qed.

(* ---- the walk ---- *)
Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world rsegs -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
Hypothesis HYP : EXV_HYP B ARx SK.
Let LAWS := eh_laws B ARx SK HYP.
(* the table runners with the memory invariant P := exvl_P mem0 (ExvB_Loop_exw.v SRr_run(_to)_tok_AJx_inv) *)
Let RUN (mem0 : word -> option byte) := SRr_run_tok_AJx_inv (SK := SK) rsegs B (@prh_pst prh_img_B) ARx LAWS
  B_prog_segs_low B_prog_tbl B_prog_tbl_ok B_prog_wx (exvl_P mem0) (exvl_PLAW mem0).
Let RUNTO (mem0 : word -> option byte) := SRr_run_to_tok_AJx_inv (SK := SK) rsegs B (@prh_pst prh_img_B) ARx LAWS
  B_prog_segs_low B_prog_tbl B_prog_tbl_ok B_prog_wx (exvl_P mem0) (exvl_PLAW mem0).

Ltac exvc_dB HB := destruct HB as (HJ & HWIN & HFRG & HFRM & HHP & HAB & HROOM & HLED & HCNT &
  R2 & R8 & R9 & R18 & R24 & R25 & R26 & R19 & R3 & R4 & HSAV & HSLOT & HFLAG & HSRC & HINB & HWD & HSINB &
  HQRA & HTREE).
Ltac exvc_dP HP := destruct HP as (HFN & PFZ & PCID & P10 & P11 & PCUR & PQ8 & PCH & PSPQ & PQD & PWIN & PSRC &
  PINB & PLEN & PI0 & PDEP & PDEPN & PDL & PWD & PSINB & PSX & PSQ & PV & PLED & PMN).
Ltac exvc_dJ HJ := destruct HJ as (JAR & JLY & JSEC & JWLE & JAOS & JFRAMES & JNEV & JK & JOUT & JBLK & JIMG &
  JFRU & JFREED & JPRES & JSTK & JEXTRA & JQT).

(* the geometry of a cut: where the cursor, the realigned frame base and the fake frame are *)
Lemma exvc_geom : forall E lyc Sc Hpc Wc regs memc mdc k pos,
  EXV_PRE B ARx E -> EXB (fx := fx) B ARx SK E lyc Sc Hpc Wc regs memc mdc k pos ->
  2 ^ 46 <= exv_sp E /\ exv_sp E <= e_q E /\ e_q E mod 8 = 0 /\ e_q E + 40 <= exv_sp E + e_d E /\
  exv_sp E + e_d E <= 2 ^ 47 /\ alloc_ceiling <= exv_sp E /\
  exv_s1 E <= exv_sp E - 288 /\ exv_sp E - 320 < exv_s1 E /\ exv_s1 E mod 32 = 0 /\
  (forall a, exv_sp E - exv_STK E <= a < exv_sp E + e_d E -> apresent (w_H Wc) memc a) /\
  ARx lyc Sc Hpc Wc memc mdc /\ 0 <= exv_STK E /\
  frame_addr lyc 1 pos + 128 <= alloc_ceiling /\ ly_stk_hi lyc <= 2 ^ 47.
Proof.
intros E lyc Sc Hpc Wc regs memc mdc k pos HP HB.
unfold EXV_PRE in HP. cbv zeta in HP. unfold EXB in HB. cbv zeta in HB.
pose proof alloc_ceiling_val as (AC1 & AC2).
pose proof HP as HP0. exvc_dP HP. pose proof HB as HB0. exvc_dB HB. pose proof HJ as HJ0. exvc_dJ HJ.
pose proof HFN as ((_ & _ & _ & _ & _ & EA & _) & _). destruct EA as (_ & HSTK0 & _).
destruct JSTK as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9).
assert (Hsp : alloc_ceiling + exv_STK E <= exv_sp E) by (unfold exv_sp in *; lia).
assert (Hs1 : exv_s1 E <= exv_sp E - 288 /\ exv_sp E - 320 < exv_s1 E /\ exv_s1 E mod 32 = 0)
  by (pose proof (exv_s1_le E); lia).
assert (Hfr : frame_addr lyc 1 pos + 128 <= alloc_ceiling).
{ assert (HIN : In (1, pos) (frames Sc)) by (rewrite JFRAMES; left; reflexivity).
  destruct (alx_sep _ _ _ LAWS lyc Sc Hpc Wc memc mdc JAR) as (_ & HF).
  rewrite Forall_forall in HF. specialize (HF (1, pos) HIN). cbn [fst snd] in HF.
  assert (HB1 : fs_frame_bytes 1 = 128) by (vm_compute; reflexivity). lia. }
destruct JLY as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ehi & _).
unfold exv_sp in *.
repeat (split; [lia|]). split; [intros a Ha; apply JPRES; lia|].
split; [exact JAR|]. split; [exact HSTK0|]. split; [exact Hfr | lia].
Qed.

(* the tree node v (when v is not NULL): below 2 ^ 47 (ExvOpen's exv_foot_rng), 8-aligned, apart from the cursor
   (EXV_PRE's footprint clause), its +40 word the count, its 56 bytes addressable and off the shadow band *)
Lemma exvc_node_facts : forall E lyc Sc Hpc Wc regs memc mdc k pos (o : bool),
  EXV_PRE B ARx E -> EXB B ARx SK E lyc Sc Hpc Wc regs memc mdc k pos ->
  e_v E <> 0 -> PjTree.tag (e_t E) = (if o then 6 else 5) ->
  0 <= e_v E /\ e_v E + 56 <= 2 ^ 47 /\ e_v E mod 8 = 0 /\
  (e_v E + 56 <= e_q E \/ e_q E + 40 <= e_v E) /\
  0 <= Z.of_nat (exv_count (e_t E)) < 2 ^ 64 /\
  val_mem rsegs (mrestrict (w_H Wc) memc) (e_v E + 40) 8 (Z.of_nat (exv_count (e_t E))) /\
  range_addressable (aview rsegs (w_H Wc) memc) SHADOW_OFF (e_v E) 56 /\
  (forall x, e_v E <= x < e_v E + 56 -> ~ (SHADOW_OFF <= x < SHADOW_OFF + 17592186044416)).
Proof.
intros E lyc Sc Hpc Wc regs memc mdc k pos o HP HB Hv0 Htag.
pose proof alloc_ceiling_val as (AC1 & AC2).
destruct (exvc_geom E lyc Sc Hpc Wc regs memc mdc k pos HP HB) as
  (Gsp46 & Gspq & Gq8 & Gqd & Gtop & Gac & Gs1a & Gs1b & Gs1c & Gpres & GAR & GSTK & Gfr & Ghi).
pose proof HP as HP0. unfold EXV_PRE in HP0. cbv zeta in HP0. exvc_dP HP0.
pose proof HB as HB0. unfold EXB in HB0. cbv zeta in HB0. exvc_dB HB0.
destruct HTREE as [Hv | (Hnd & Hhome & Hra & Hhull)]; [exfalso; exact (Hv0 Hv)|].
destruct PV as [Hv | (_ & _ & PFOOT)]; [exfalso; exact (Hv0 Hv)|].
pose proof (exv_foot_rng B ARx SK HYP lyc Sc Hpc Wc memc mdc (e_Lam E) (e_peak E) (e_cnt E) (e_fail E) (e_ran E) (e_most E) (e_own E)
  regs (e_v E) (e_t E) (e_D E) GAR HLED Hnd Hhome Ghi) as FOOT.
assert (F0 := FOOT (e_v E) ltac:(left; lia)). assert (F55 := FOOT (e_v E + 55) ltac:(left; lia)).
destruct (exvc_node_count _ _ _ _ _ o Hnd Htag) as (Hv8 & Hcnt & Vcnt).
split; [lia|]. split; [lia|]. split; [exact Hv8|]. split.
{ destruct (Z.lt_ge_cases (e_v E) (e_q E)) as [H1|H1].
  - destruct (Z.lt_ge_cases (e_q E) (e_v E + 56)) as [H2|H2]; [|left; lia].
    exfalso. destruct (PFOOT (e_q E) ltac:(left; lia)) as (_ & Hq & _). apply Hq. lia.
  - right. destruct (Z.lt_ge_cases (e_v E) (e_q E + 40)) as [H2|H2]; [|lia].
    exfalso. destruct (PFOOT (e_v E) ltac:(left; lia)) as (_ & Hq & _). apply Hq. lia. }
split; [exact Hcnt|]. split; [exact Vcnt|]. split; [exact Hra|].
intros x Hx. pose proof (@cf_head_nonneg cp) as CH0. unfold SHADOW_OFF.
destruct Hhome as [(b & m & Hin & H1 & H2) | [(cid & ps & Hin & H1 & H2) | (H1 & H2)]].
- pose proof HLED as (_ & _ & HBL & _). rewrite Forall_forall in HBL.
  destruct (HBL (b, m) Hin) as (Hk0 & Hblk & _ & _ & _). cbn [fst snd] in *.
  destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ _ _ GAR Hblk) as (_ & _ & _ & Happ & _).
  assert (Hrq : m + cf_head <= req_size (m + cf_head))
    by (unfold req_size; destruct (Z.eqb_spec (m + cf_head) 0); lia).
  unfold in_app, kLowShadowBeg, kHighMemBeg in Happ. lia.
- destruct (alx_frames _ _ _ LAWS _ _ _ _ _ _ _ _ GAR Hin) as (_ & Happ & _).
  unfold in_app, kLowShadowBeg, kHighMemBeg in Happ. lia.
- assert (HS2 : spZ regs = exv_s1 E) by (unfold spZ; rewrite R2; apply unsigned_lit_small; lia). lia.
Qed.

(* the two arms of the compare, as the post asks them *)
Lemma exvc_res_eq : forall o acc t (dl dlc : Z),
  Z.of_nat (exv_count t) < 2 ^ 64 ->
  (dlc = 1 <-> dl = 1 \/ ~ exv_pref o acc t) ->
  Z.of_nat (length acc) mod 2 ^ 64 = Z.of_nat (exv_count t) ->
  (dlc = 1 <-> dl = 1 \/ t <> PjGrammar.mk o (rev acc)).
Proof.
intros o acc t dl dlc Hc Hiff Heq. rewrite Hiff. split.
- intros [H|H]; [left; exact H | right; intros Ht; apply H; rewrite Ht; apply exvc_pref_mk].
- intros [H|H]; [left; exact H | right; intros Hp; apply H].
  pose proof (exvc_pref_len o acc t Hp) as Hl.
  rewrite Z.mod_small in Heq by lia.
  apply exvc_eq_of_pref; [exact Hp | lia].
Qed.

Lemma exvc_res_ne : forall o acc t, Z.of_nat (exv_count t) < 2 ^ 64 ->
  Z.of_nat (length acc) mod 2 ^ 64 <> Z.of_nat (exv_count t) -> t <> PjGrammar.mk o (rev acc).
Proof.
intros o acc t Hc Hne Ht. subst t. apply Hne. rewrite exvc_count_mk, length_rev in *.
rewrite Z.mod_small by lia. reflexivity.
Qed.

Lemma exvc_U_mod : forall E n v, ew E n = Z_to_bv 64 v -> U E (SOff n 0) = v mod 2 ^ 64.
Proof.
intros E n v H. rewrite U_SOff, H, Z.add_0_r, Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
apply zcanon_id. pose proof (Z.mod_pos_bound v (2 ^ 64) ltac:(lia)). unfold M64. lia.
Qed.

(* ExvOpen's T1, rebound onto the old-pin kit (lib/B/Prog/ExvB_Open_kt.v blob 7b89f08a32f8, cold/h-rw-pre-7-b-ex_value-open
   ed8cdf7ea24e, on the rebind base): EXB across a stretch that writes only ex_value's frame area and the FP cursor
   cells, given the memnorm keep from the entry memory to the end memory *)
Let KT := exv_kt B ARx SK HYP.

(* ---- the three symbolic states ---- *)
(* B 0x83f68 (the depth decrement): a3 = q + 16, the spill 104(s1) = shadow_addr (q + 16), in->depth = dep + 1 *)
Definition exvc_t_regs : list sv := sr_set sr_atoms 13%bv (SOff 19 16).
Definition exvc_t_mem : smem :=
[ YP09.mkRegion (Some 9%nat) 104 112 0 0 [YP09.mkChunk 104 (CVal 8 (exvc_shx 16))];
  YP09.mkRegion (Some 19%nat) 16 20 16 20 [YP09.mkChunk 16 (CVal 4 (SOff 32 1))] ].
Definition exvc_t_facts : list (nat * afact) :=
[ (9%nat, mkAF (2 ^ 46) (2 ^ 47) 3); (19%nat, mkAF (2 ^ 46) (2 ^ 47 - 40) 3);
  (25%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (32%nat, mkAF 0 32 0) ].
Definition ss_exvc_t : sstate := mkSS EXVC_DEC exvc_t_regs exvc_t_mem None (mkFacts exvc_t_facts [] []).
Definition exvc_t_SH : list shent := [mkSHE 19 0 40].
(* B 0x83f30 (the count compare): a0 = v, a1 = the count read, v->n, in->differs = dlc *)
Definition exvc_c_mem : smem :=
[ YP09.mkRegion (Some 10%nat) 40 48 0 0 [YP09.mkChunk 40 (CVal 8 (SOff 32 0))];
  YP09.mkRegion (Some 19%nat) 32 36 32 36 [YP09.mkChunk 32 (CVal 4 (SOff 33 0))] ].
Definition exvc_c_facts : list (nat * afact) :=
[ (10%nat, mkAF 0 (2 ^ 47 - 56) 3); (19%nat, mkAF (2 ^ 46) (2 ^ 47 - 40) 3);
  (25%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (32%nat, mkAF 0 (2 ^ 64 - 1) 0); (33%nat, mkAF 0 1 0) ].
Definition ss_exvc_c : sstate := mkSS EXVC_CMP sr_atoms exvc_c_mem None (mkFacts exvc_c_facts [] []).
Definition exvc_c_SH : list shent := [mkSHE 10 40 48; mkSHE 19 0 40].
(* B 0x83f24 (the cut): the spills 96(s1) = q + 16 and 152(s1) = vv *)
Definition exvc_h_mem : smem :=
[ YP09.mkRegion (Some 9%nat) 96 160 0 0
    [YP09.mkChunk 96 (CVal 8 (SOff 19 16)); YP09.mkChunk 152 (CVal 8 (SOff 32 0))] ].
Definition exvc_h_facts : list (nat * afact) :=
[ (9%nat, mkAF (2 ^ 46) (2 ^ 47) 3); (19%nat, mkAF (2 ^ 46) (2 ^ 47 - 40) 3);
  (25%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (32%nat, mkAF 0 (2 ^ 47 - 56) 3) ].
Definition ss_exvc_h : sstate := mkSS EXVC_PC sr_atoms exvc_h_mem None (mkFacts exvc_h_facts [] []).
Definition exvc_h_SH : list shent := [].

(* the awr side condition of a run: every written byte lies in the caller-window journal's stack window *)
Ltac exvc_awr U1 U2 :=
lazymatch goal with |- awr_ok ?Ex ?rs _ _ _ _ _ _ _ =>
let rs' := eval vm_compute in rs in change rs with rs' end;
repeat (apply exw_awr_cons; [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val];
let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
cbn [ew ewset Nat.eqb] in Ha; rewrite ?U1, ?U2 in Ha; left; lia | ]);
apply awr_ok_nil.

(* ---- B 0x83f68 to the CX cut: the shadow check of in->depth, the depth decrement (UBSan check B 0x83f7c not
   taken: dep < dep + 1, decided in the run from the atom's range), s5 = 0 ---- *)
Lemma exvc_tail : forall n,
  (forall fx0 : YK11.FPState, CUT_CX (fx := fx0) B ARx SK n) ->
  forall E lyc Sc Hpc Wc regs memc mdc k pos (u : PjTree.jv) (ip dlf : Z),
  e_n E = n -> EXV_PRE B ARx E -> EXB B ARx SK E lyc Sc Hpc Wc regs memc mdc k pos ->
  e_dep E + 1 <= 32 ->
  prhex_cur Wc memc (e_q E) (e_x0 E + ip) (e_x0 E + exv_len E) (e_dep E + 1) (e_scr E) dlf ->
  0 <= ip <= exv_len E -> (dlf = 0 \/ dlf = 1) ->
  exv_V E = Some (u, skipn (Z.to_nat ip) (e_x E)) ->
  (dlf = 1 <-> e_dl E = 1 \/ (e_v E <> 0 /\ e_t E <> u)) ->
  getr regs 13 = w64 (e_q E + 16) ->
  exv_spill E Wc memc 104 (shadow_addr (e_q E + 16)) ->
  SRr rsegs Wc (cfg_at (fx := fx) rsegs EXVC_DEC regs memc mdc) (EXV_POST B ARx SK E).
Proof.
intros n HX E lyc Sc Hpc Wc regs memc mdc k pos u ip dlf Hn HP HB Hd32 HCUR Hip Hdlf HV Hres R13 SP104.
pose proof alloc_ceiling_val as (AC1 & AC2).
destruct (exvc_geom E lyc Sc Hpc Wc regs memc mdc k pos HP HB) as
  (Gsp46 & Gspq & Gq8 & Gqd & Gtop & Gac & Gs1a & Gs1b & Gs1c & Gpres & GAR & GSTK & Gfr & Ghi).
pose proof HP as HP0. unfold EXV_PRE in HP0. cbv zeta in HP0. exvc_dP HP0.
pose proof HB as HB0. unfold EXB in HB0. cbv zeta in HB0. exvc_dB HB0.
destruct HCUR as (CP & CE & CD & CS & CL).
remember (Ereg regs [Z_to_bv 64 (e_dep E)]) as Ev eqn:HEv.
assert (E9 : ew Ev 9 = Z_to_bv 64 (exv_s1 E)) by (subst Ev; rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact R9).
assert (E19 : ew Ev 19 = Z_to_bv 64 (e_q E)) by (subst Ev; rewrite (ew_Ereg_nat regs _ 19 19%bv eq_refl); exact R19).
assert (E25 : ew Ev 25 = Z_to_bv 64 SHADOW_OFF)
  by (subst Ev; rewrite (ew_Ereg_nat regs _ 25 25%bv eq_refl); exact R25).
assert (E32 : ew Ev 32 = Z_to_bv 64 (e_dep E)) by (subst Ev; exact (ew_Ereg_extra regs _ 0)).
assert (U9 : bv_unsigned (ew Ev 9) = exv_s1 E) by (rewrite E9; apply unsigned_lit_small; lia).
assert (U19 : bv_unsigned (ew Ev 19) = e_q E) by (rewrite E19; apply unsigned_lit_small; lia).
assert (U25 : bv_unsigned (ew Ev 25) = SHADOW_OFF) by (rewrite E25; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U32 : bv_unsigned (ew Ev 32) = e_dep E) by (rewrite E32; apply unsigned_lit_small; lia).
assert (AGE : env_agree 32 (Ereg regs [Z_to_bv 64 (e_dep E)]) Ev) by (rewrite <- HEv; apply env_agree_refl).
assert (HS : st_ok rsegs Ev ss_exvc_t (restrict (w_H Wc) (mkst regs (Z_to_bv 64 EXVC_DEC) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. unfold ss_exvc_t. apply exw_st_ok_full.
  - unfold exvc_t_regs. apply regs_ok_pin; [rewrite HEv; apply regs_ok_Ereg | intros X; discriminate X |].
    cbn [sv_denot]. rewrite U19. exact R13.
  - vm_compute. reflexivity.
  - unfold exvc_t_mem. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    + rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
      apply (chunk_ok_val rsegs Ev _ (exv_s1 E) 104 8 (exvc_shx 16) (shadow_addr (e_q E + 16)));
        [ rewrite (exvc_denot_shx Ev 16 (e_q E) SHADOW_OFF E19 E25) by (unfold SHADOW_OFF; lia); reflexivity
        | unfold shadow_addr, SHADOW_OFF; cbn; lia | zside | exact SP104 ].
    + rewrite U19. split; [lia|]. split; [lia|]. split.
      { intros o Ho. apply (apresent_writable rsegs). apply Gpres. lia. }
      constructor; [|constructor].
      apply (chunk_ok_val rsegs Ev _ (e_q E) 16 4 (SOff 32 1) (e_dep E + 1));
        [ cbn [sv_denot]; rewrite U32; reflexivity | cbn; lia | zside | exact CD ].
  - apply pairwise_disjoint_of_extents. unfold exvc_t_mem. cbn [map]. unfold extent_of_region.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U19.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
  - split; [|split; [exact I | exact I]].
    cbn [f_atoms atoms_ok exvc_t_facts]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U9, U19, U25, U32. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
    unfold SHADOW_OFF. repeat split; lia. }
assert (HBx : U Ev EXVC_SB = SHADOW_OFF)
  by (unfold EXVC_SB; rewrite (U_atom Ev 25 SHADOW_OFF E25) by (unfold SHADOW_OFF; lia); reflexivity).
assert (SHOK : sh_ok rsegs EXVC_SB exvc_t_SH Ev (mrestrict (w_H Wc) memc)).
{ unfold exvc_t_SH. constructor; [|constructor].
  apply (shent_ok_of_range rsegs (w_H Wc) memc Ev EXVC_SB 19 (e_q E) 40 (e_q E) 0 40 HQRA HBx);
    [rewrite (U_atom Ev 19 (e_q E) E19) by lia; reflexivity | lia | lia |].
  intros x Hx. unfold SHADOW_OFF. lia. }
assert (HPM : exvl_P (e_mem E) memc) by exact (proj2 HROOM).
unfold cfg_at. change (w64 EXVC_DEC) with (Z_to_bv 64 EXVC_DEC).
exw_run_to (RUNTO (e_mem E)) HS HJ SHOK HPM EXVC_END.
{ exvc_awr U9 U19. }
exw_kept_of HFr (fun a => e_q E + 16 <= a < e_q E + 20) ltac:(fun h => cbn [ew ewset Nat.eqb] in h; rewrite ?U19 in h).
rename KEPT into K1. rename HG into G1. clear HF HFr.
prreg HS (21%bv : bv 5) R21'.
pose proof (exw_region_nth rsegs _ _ _ 1 _ HS eq_refl) as RQ. cbn [ms_mem restrict] in RQ.
pose proof (exw_field rsegs _ _ 19%nat (e_q E) _ _ _ _ _ 16 4 (SOff 32 0) (e_dep E) RQ
  ltac:(cbn [ew ewset Nat.eqb]; exact U19) ltac:(left; reflexivity)
  ltac:(cbn [sv_denot ew ewset Nat.eqb]; rewrite U32, Z.add_0_r; reflexivity) ltac:(cbn; lia) ltac:(zside)) as VD.
pose proof (regs_kept_of_st_ok rsegs _ _ _ regs _ [2; 3; 4; 8; 9; 18; 19; 24; 25; 26]%bv HS AGE
  ltac:(vm_compute; reflexivity)) as RK.
pmkst HS.
eapply (HX fx E lyc Sc Hpc Wc _ _ _ k pos 0 Hn HP).
- apply (KT E lyc Sc Hpc Wc regs memc mdc k pos _ _ _ k HP HB HJ).
  + intros a Ha _ Hn'. apply K1; [exact Ha|]. intros Hq. apply Hn'. split; [|lia].
    exists (e_q E + 16, e_q E + 20). split; [unfold exv_FP; right; right; left; reflexivity | cbn [fst snd]; lia].
  + intros a Ha. exact (apresent_grows _ _ _ a G1 Ha).
  + exact HPM.
  + exact RK.
- exact R21'.
- unfold EXV_RES. exists ip, (e_dep E), dlf. split.
  + split; [|split; [|split; [|split]]].
    * apply (exw_val_kept rsegs (w_H Wc) memc); [|exact CP]. intros x Hx. apply K1; lia.
    * apply (exw_val_kept rsegs (w_H Wc) memc); [|exact CE]. intros x Hx. apply K1; lia.
    * exact VD.
    * apply (exw_val_kept rsegs (w_H Wc) memc); [|exact CS]. intros x Hx. apply K1; lia.
    * apply (exw_val_kept rsegs (w_H Wc) memc); [|exact CL]. intros x Hx. apply K1; lia.
  + split; [exact Hdlf|]. rewrite HV. split; [reflexivity|]. split; [|split; [reflexivity | exact Hres]].
    rewrite length_skipn. unfold exv_len in *. lia.
Qed.

(* ---- B 0x83f30 (v is not NULL) to B 0x83f68: the ASan check of v->n (granule [v + 40, v + 48) at shadow 0), the
   count compare `beq a1, a0`, and in->differs = 1 when the counts differ (ASan check of q + 32 at shadow 0) ---- *)
Lemma exvc_cmp : forall n,
  (forall fx0 : YK11.FPState, CUT_CX (fx := fx0) B ARx SK n) ->
  forall E lyc Sc Hpc Wc regs memc mdc k pos (o : bool) (acc : list (list Z * PjTree.jv)) (ip dlc : Z),
  e_n E = n -> EXV_PRE B ARx E -> EXB B ARx SK E lyc Sc Hpc Wc regs memc mdc k pos ->
  e_dep E + 1 <= 32 ->
  prhex_cur Wc memc (e_q E) (e_x0 E + ip) (e_x0 E + exv_len E) (e_dep E + 1) (e_scr E) dlc ->
  0 <= ip <= exv_len E -> (dlc = 0 \/ dlc = 1) ->
  exv_V E = Some (PjGrammar.mk o (rev acc), skipn (Z.to_nat ip) (e_x E)) ->
  e_v E <> 0 -> PjTree.tag (e_t E) = (if o then 6 else 5) ->
  (dlc = 1 <-> e_dl E = 1 \/ ~ exv_pref o acc (e_t E)) ->
  getr regs 10 = w64 (e_v E) -> getr regs 11 = w64 (Z.of_nat (length acc)) -> getr regs 13 = w64 (e_q E + 16) ->
  exv_spill E Wc memc 104 (shadow_addr (e_q E + 16)) ->
  SRr rsegs Wc (cfg_at (fx := fx) rsegs EXVC_CMP regs memc mdc) (EXV_POST B ARx SK E).
Proof.
intros n HX E lyc Sc Hpc Wc regs memc mdc k pos o acc ip dlc Hn HP HB Hd32 HCUR Hip Hdlc HV Hv0 Htag Hiff
  R10 R11 R13 SP104.
pose proof alloc_ceiling_val as (AC1 & AC2).
destruct (exvc_geom E lyc Sc Hpc Wc regs memc mdc k pos HP HB) as
  (Gsp46 & Gspq & Gq8 & Gqd & Gtop & Gac & Gs1a & Gs1b & Gs1c & Gpres & GAR & GSTK & Gfr & Ghi).
destruct (exvc_node_facts E lyc Sc Hpc Wc regs memc mdc k pos o HP HB Hv0 Htag) as
  (Nv0 & Nv47 & Nv8 & Nvq & Ncnt & Vcnt & Nra & Nap).
pose proof HB as HB0. unfold EXB in HB0. cbv zeta in HB0. exvc_dB HB0.
pose proof HCUR as (CP & CE & CD & CS & CL).
remember (Ereg regs [Z_to_bv 64 (Z.of_nat (exv_count (e_t E))); Z_to_bv 64 dlc]) as Ev eqn:HEv.
assert (E10 : ew Ev 10 = Z_to_bv 64 (e_v E))
  by (subst Ev; rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact R10).
assert (E11 : ew Ev 11 = Z_to_bv 64 (Z.of_nat (length acc)))
  by (subst Ev; rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact R11).
assert (E19 : ew Ev 19 = Z_to_bv 64 (e_q E)) by (subst Ev; rewrite (ew_Ereg_nat regs _ 19 19%bv eq_refl); exact R19).
assert (E25 : ew Ev 25 = Z_to_bv 64 SHADOW_OFF)
  by (subst Ev; rewrite (ew_Ereg_nat regs _ 25 25%bv eq_refl); exact R25).
assert (E32 : ew Ev 32 = Z_to_bv 64 (Z.of_nat (exv_count (e_t E)))) by (subst Ev; exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew Ev 33 = Z_to_bv 64 dlc) by (subst Ev; exact (ew_Ereg_extra regs _ 1)).
assert (U10 : bv_unsigned (ew Ev 10) = e_v E) by (rewrite E10; apply unsigned_lit_small; lia).
assert (U19 : bv_unsigned (ew Ev 19) = e_q E) by (rewrite E19; apply unsigned_lit_small; lia).
assert (U25 : bv_unsigned (ew Ev 25) = SHADOW_OFF) by (rewrite E25; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U32 : bv_unsigned (ew Ev 32) = Z.of_nat (exv_count (e_t E))) by (rewrite E32; apply unsigned_lit_small; lia).
assert (U33 : bv_unsigned (ew Ev 33) = dlc) by (rewrite E33; apply unsigned_lit_small; lia).
assert (AGE : env_agree 32 (Ereg regs [Z_to_bv 64 (Z.of_nat (exv_count (e_t E))); Z_to_bv 64 dlc]) Ev)
  by (rewrite <- HEv; apply env_agree_refl).
assert (HS : st_ok rsegs Ev ss_exvc_c (restrict (w_H Wc) (mkst regs (Z_to_bv 64 EXVC_CMP) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. unfold ss_exvc_c. apply exw_st_ok_full.
  - rewrite HEv. apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - unfold exvc_c_mem. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    + rewrite U10. split; [lia|]. split; [lia|]. split; [intros o' Ho'; lia|]. constructor; [|constructor].
      apply (chunk_ok_val rsegs Ev _ (e_v E) 40 8 (SOff 32 0) (Z.of_nat (exv_count (e_t E))));
        [ cbn [sv_denot]; rewrite U32, Z.add_0_r; reflexivity | cbn; lia | zside | exact Vcnt ].
    + rewrite U19. split; [lia|]. split; [lia|]. split.
      { intros o' Ho'. apply (apresent_writable rsegs). apply Gpres. lia. }
      constructor; [|constructor].
      apply (chunk_ok_val rsegs Ev _ (e_q E) 32 4 (SOff 33 0) dlc);
        [ cbn [sv_denot]; rewrite U33, Z.add_0_r; reflexivity | cbn; lia | zside | exact CL ].
  - apply pairwise_disjoint_of_extents. unfold exvc_c_mem. cbn [map]. unfold extent_of_region.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U10, U19.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
  - split; [|split; [exact I | exact I]].
    cbn [f_atoms atoms_ok exvc_c_facts]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U10, U19, U25, U32, U33. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
    unfold SHADOW_OFF. repeat split; lia. }
assert (HBx : U Ev EXVC_SB = SHADOW_OFF)
  by (unfold EXVC_SB; rewrite (U_atom Ev 25 SHADOW_OFF E25) by (unfold SHADOW_OFF; lia); reflexivity).
assert (SHOK : sh_ok rsegs EXVC_SB exvc_c_SH Ev (mrestrict (w_H Wc) memc)).
{ unfold exvc_c_SH. constructor; [|constructor; [|constructor]].
  - apply (shent_ok_of_range rsegs (w_H Wc) memc Ev EXVC_SB 10 (e_v E) 56 (e_v E) 40 48 Nra HBx);
      [rewrite (U_atom Ev 10 (e_v E) E10) by lia; reflexivity | lia | lia |].
    intros x Hx. apply Nap. lia.
  - apply (shent_ok_of_range rsegs (w_H Wc) memc Ev EXVC_SB 19 (e_q E) 40 (e_q E) 0 40 HQRA HBx);
      [rewrite (U_atom Ev 19 (e_q E) E19) by lia; reflexivity | lia | lia |].
    intros x Hx. unfold SHADOW_OFF. lia. }
assert (U11 : U Ev (SOff 11 0) = Z.of_nat (length acc) mod 2 ^ 64) by exact (exvc_U_mod Ev 11 _ E11).
assert (U32' : U Ev (SOff 32 0) = Z.of_nat (exv_count (e_t E))) by (apply (U_atom Ev 32 _ E32); lia).
assert (HPM : exvl_P (e_mem E) memc) by exact (proj2 HROOM).
unfold cfg_at. change (w64 EXVC_CMP) with (Z_to_bv 64 EXVC_CMP).
exw_run (RUN (e_mem E)) HS HJ SHOK HPM.
{ exvc_awr U10 U19. }
exw_kept_of HFr (fun a => e_q E + 32 <= a < e_q E + 36) ltac:(fun h => cbn [ew ewset Nat.eqb] in h; rewrite ?U19 in h).
rename KEPT into K1. rename HG into G1. clear HF HFr.
exw_branch HS SHOK.
- (* the counts agree: in->differs unchanged *)
  rewrite branch_eq_U in Hc. apply Z.eqb_eq in Hc. rewrite U11, U32' in Hc.
  exw_run_to (RUNTO (e_mem E)) HS HJ SHOK HPM EXVC_DEC.
  { exvc_awr U10 U19. }
  exw_kept_of HFr (fun a => e_q E + 32 <= a < e_q E + 36) ltac:(fun h => cbn [ew ewset Nat.eqb] in h; rewrite ?U19 in h).
  rename KEPT into K2. rename HG into G2. clear HF HFr.
  pose proof (exw_region_nth rsegs _ _ _ 1 _ HS eq_refl) as RQ. cbn [ms_mem restrict] in RQ.
  pose proof (exw_field rsegs _ _ 19%nat (e_q E) _ _ _ _ _ 32 4 (SOff 33 0) dlc RQ
    ltac:(cbn [ew ewset Nat.eqb]; exact U19) ltac:(left; reflexivity)
    ltac:(cbn [sv_denot ew ewset Nat.eqb]; rewrite U33, Z.add_0_r; reflexivity) ltac:(cbn; lia) ltac:(zside)) as VL.
  pose proof (regs_kept_of_st_ok rsegs _ _ _ regs _ [2; 3; 4; 8; 9; 18; 19; 24; 25; 26]%bv HS AGE
    ltac:(vm_compute; reflexivity)) as RK.
  pose proof (regs_kept_of_st_ok rsegs _ _ _ regs _ [13]%bv HS AGE ltac:(vm_compute; reflexivity)
    13%bv (or_introl eq_refl)) as RK13.
  lazymatch type of HS with st_ok _ _ _ (restrict _ ?mx) =>
    assert (KA : forall a, 0 <= a < 2 ^ 64 -> ~ (e_q E + 32 <= a < e_q E + 36) ->
      aview rsegs (w_H Wc) (ms_mem mx) a = aview rsegs (w_H Wc) memc a)
      by (intros a Ha Hna; rewrite K2, K1 by assumption; reflexivity);
    assert (GA : forall a, apresent (w_H Wc) memc a -> apresent (w_H Wc) (ms_mem mx) a)
      by (intros a Ha; apply (apresent_grows _ _ _ a G2), (apresent_grows _ _ _ a G1), Ha) end.
  pmkst HS.
  eapply (exvc_tail n HX E lyc Sc Hpc Wc _ _ _ k pos (PjGrammar.mk o (rev acc)) ip dlc Hn HP).
  + apply (KT E lyc Sc Hpc Wc regs memc mdc k pos _ _ _ k HP HB HJ); [| exact GA | exact HPM | exact RK].
    intros a Ha _ Hn'. apply KA; [exact Ha|]. intros Hq. apply Hn'. split; [|lia].
    exists (e_q E + 32, e_q E + 36). split; [unfold exv_FP; right; right; right; left; reflexivity | cbn [fst snd]; lia].
  + exact Hd32.
  + split; [|split; [|split; [|split]]].
    * apply (exw_val_kept rsegs (w_H Wc) memc); [|exact CP]. intros x Hx. apply KA; lia.
    * apply (exw_val_kept rsegs (w_H Wc) memc); [|exact CE]. intros x Hx. apply KA; lia.
    * apply (exw_val_kept rsegs (w_H Wc) memc); [|exact CD]. intros x Hx. apply KA; lia.
    * apply (exw_val_kept rsegs (w_H Wc) memc); [|exact CS]. intros x Hx. apply KA; lia.
    * exact VL.
  + exact Hip.
  + exact Hdlc.
  + exact HV.
  + rewrite (exvc_res_eq o acc (e_t E) (e_dl E) dlc ltac:(lia) Hiff Hc). tauto.
  + cbn [ms_regs restrict] in RK13. rewrite RK13. exact R13.
  + apply (exw_val_kept rsegs (w_H Wc) memc); [|exact SP104]. intros x Hx. apply KA; lia.
- (* the counts differ: in->differs = 1 *)
  rewrite branch_eq_U in Hc. apply Z.eqb_neq in Hc. rewrite U11, U32' in Hc.
  exw_run_to (RUNTO (e_mem E)) HS HJ SHOK HPM EXVC_DEC.
  { exvc_awr U10 U19. }
  exw_kept_of HFr (fun a => e_q E + 32 <= a < e_q E + 36) ltac:(fun h => cbn [ew ewset Nat.eqb] in h; rewrite ?U19 in h).
  rename KEPT into K2. rename HG into G2. clear HF HFr.
  pose proof (exw_region_nth rsegs _ _ _ 1 _ HS eq_refl) as RQ. cbn [ms_mem restrict] in RQ.
  pose proof (exw_field rsegs _ _ 19%nat (e_q E) _ _ _ _ _ 32 4 (SLit 1) 1 RQ
    ltac:(cbn [ew ewset Nat.eqb]; exact U19) ltac:(left; reflexivity)
    ltac:(cbn [sv_denot]; reflexivity) ltac:(cbn; lia) ltac:(zside)) as VL.
  pose proof (regs_kept_of_st_ok rsegs _ _ _ regs _ [2; 3; 4; 8; 9; 18; 19; 24; 25; 26]%bv HS AGE
    ltac:(vm_compute; reflexivity)) as RK.
  pose proof (regs_kept_of_st_ok rsegs _ _ _ regs _ [13]%bv HS AGE ltac:(vm_compute; reflexivity)
    13%bv (or_introl eq_refl)) as RK13.
  lazymatch type of HS with st_ok _ _ _ (restrict _ ?mx) =>
    assert (KA : forall a, 0 <= a < 2 ^ 64 -> ~ (e_q E + 32 <= a < e_q E + 36) ->
      aview rsegs (w_H Wc) (ms_mem mx) a = aview rsegs (w_H Wc) memc a)
      by (intros a Ha Hna; rewrite K2, K1 by assumption; reflexivity);
    assert (GA : forall a, apresent (w_H Wc) memc a -> apresent (w_H Wc) (ms_mem mx) a)
      by (intros a Ha; apply (apresent_grows _ _ _ a G2), (apresent_grows _ _ _ a G1), Ha) end.
  pmkst HS.
  eapply (exvc_tail n HX E lyc Sc Hpc Wc _ _ _ k pos (PjGrammar.mk o (rev acc)) ip 1 Hn HP).
  + apply (KT E lyc Sc Hpc Wc regs memc mdc k pos _ _ _ k HP HB HJ); [| exact GA | exact HPM | exact RK].
    intros a Ha _ Hn'. apply KA; [exact Ha|]. intros Hq. apply Hn'. split; [|lia].
    exists (e_q E + 32, e_q E + 36). split; [unfold exv_FP; right; right; right; left; reflexivity | cbn [fst snd]; lia].
  + exact Hd32.
  + split; [|split; [|split; [|split]]].
    * apply (exw_val_kept rsegs (w_H Wc) memc); [|exact CP]. intros x Hx. apply KA; lia.
    * apply (exw_val_kept rsegs (w_H Wc) memc); [|exact CE]. intros x Hx. apply KA; lia.
    * apply (exw_val_kept rsegs (w_H Wc) memc); [|exact CD]. intros x Hx. apply KA; lia.
    * apply (exw_val_kept rsegs (w_H Wc) memc); [|exact CS]. intros x Hx. apply KA; lia.
    * exact VL.
  + exact Hip.
  + right; reflexivity.
  + exact HV.
  + split; intros _; [right; split; [exact Hv0 | exact (exvc_res_ne o acc (e_t E) ltac:(lia) Hc)] | reflexivity].
  + cbn [ms_regs restrict] in RK13. rewrite RK13. exact R13.
  + apply (exw_val_kept rsegs (w_H Wc) memc); [|exact SP104]. intros x Hx. apply KA; lia.
Qed.

(* ---- the CC cut, B 0x83f24: the two spills, `beqz a0` on vv; to the compare (v not NULL) or straight to the
   depth decrement (vv NULL: the caller passed no tree, or ex_items' type check nulled it) ---- *)
Lemma exvc_close : forall n,
  (forall fx0 : YK11.FPState, CUT_CX (fx := fx0) B ARx SK n) -> CUT_CC (fx := fx) B ARx SK n.
Proof.
intros n HX. unfold CUT_CC. cbv zeta.
intros E lyc Sc Hpc Wc regs memc mdc k pos c acc ip vv dlc Hn HP HB Hc91 Hd32 HCUR Hip Hdlc HV HDIF R11 SP152 SP96 SP104.
pose proof alloc_ceiling_val as (AC1 & AC2).
destruct (exvc_geom E lyc Sc Hpc Wc regs memc mdc k pos HP HB) as
  (Gsp46 & Gspq & Gq8 & Gqd & Gtop & Gac & Gs1a & Gs1b & Gs1c & Gpres & GAR & GSTK & Gfr & Ghi).
pose proof HB as HB0. unfold EXB in HB0. cbv zeta in HB0. exvc_dB HB0.
pose proof HCUR as (CP & CE & CD & CS & CL).
assert (Hvvb : 0 <= vv /\ vv + 56 <= 2 ^ 47 /\ vv mod 8 = 0).
{ destruct HDIF as [(-> & _ & _) | (-> & Hv0 & Htag & _)]; [lia|].
  destruct (exvc_node_facts E lyc Sc Hpc Wc regs memc mdc k pos (c =? 123) HP HB Hv0 Htag) as (N0 & N47 & N8 & _).
  lia. }
remember (Ereg regs [Z_to_bv 64 vv]) as Ev eqn:HEv.
assert (E9 : ew Ev 9 = Z_to_bv 64 (exv_s1 E)) by (subst Ev; rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact R9).
assert (E19 : ew Ev 19 = Z_to_bv 64 (e_q E)) by (subst Ev; rewrite (ew_Ereg_nat regs _ 19 19%bv eq_refl); exact R19).
assert (E25 : ew Ev 25 = Z_to_bv 64 SHADOW_OFF)
  by (subst Ev; rewrite (ew_Ereg_nat regs _ 25 25%bv eq_refl); exact R25).
assert (E32 : ew Ev 32 = Z_to_bv 64 vv) by (subst Ev; exact (ew_Ereg_extra regs _ 0)).
assert (U9 : bv_unsigned (ew Ev 9) = exv_s1 E) by (rewrite E9; apply unsigned_lit_small; lia).
assert (U19 : bv_unsigned (ew Ev 19) = e_q E) by (rewrite E19; apply unsigned_lit_small; lia).
assert (U25 : bv_unsigned (ew Ev 25) = SHADOW_OFF) by (rewrite E25; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U32 : bv_unsigned (ew Ev 32) = vv) by (rewrite E32; apply unsigned_lit_small; lia).
assert (AGE : env_agree 32 (Ereg regs [Z_to_bv 64 vv]) Ev) by (rewrite <- HEv; apply env_agree_refl).
assert (HS : st_ok rsegs Ev ss_exvc_h (restrict (w_H Wc) (mkst regs (Z_to_bv 64 EXVC_PC) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. unfold ss_exvc_h. apply exw_st_ok_full.
  - rewrite HEv. apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - unfold exvc_h_mem. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor; [|constructor]].
    + apply (chunk_ok_val rsegs Ev _ (exv_s1 E) 96 8 (SOff 19 16) (e_q E + 16));
        [ cbn [sv_denot]; rewrite U19; reflexivity | cbn; lia | zside | exact SP96 ].
    + apply (chunk_ok_val rsegs Ev _ (exv_s1 E) 152 8 (SOff 32 0) vv);
        [ cbn [sv_denot]; rewrite U32, Z.add_0_r; reflexivity | cbn; lia | zside | exact SP152 ].
  - apply pairwise_disjoint_of_extents. unfold exvc_h_mem. cbn [map]. unfold extent_of_region.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. cbn [zpairwise_disjoint zall_disjoint]. repeat split.
  - split; [|split; [exact I | exact I]].
    cbn [f_atoms atoms_ok exvc_h_facts]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U9, U19, U25, U32. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
    unfold SHADOW_OFF. repeat split; lia. }
assert (SHOK : sh_ok rsegs EXVC_SB exvc_h_SH Ev (mrestrict (w_H Wc) memc)) by (unfold exvc_h_SH; constructor).
assert (HPM : exvl_P (e_mem E) memc) by exact (proj2 HROOM).
unfold cfg_at. change (w64 EXVC_PC) with (Z_to_bv 64 EXVC_PC).
exw_run (RUN (e_mem E)) HS HJ SHOK HPM.
{ exvc_awr U9 U19. }
exw_kept_of HFr (fun _ : Z => False) ltac:(fun h => idtac).
rename KEPT into K1. rename HG into G1. clear HF HFr.
exw_branch HS SHOK.
- (* vv = 0: no compare; in->differs as the open / loop left it *)
  rewrite branch_eq_U in Hc. apply Z.eqb_eq in Hc. rewrite (U_atom Ev 32 vv E32), U_lit in Hc by lia.
  assert (Hres : dlc = 1 <-> e_dl E = 1 \/ (e_v E <> 0 /\ e_t E <> PjGrammar.mk (c =? 123) (rev acc))).
  { destruct HDIF as [(_ & H0 & H1) | (Hvv & Hvv0 & _)]; [|exfalso; lia].
    destruct (Z.eq_dec (e_v E) 0) as [Hz|Hz].
    - rewrite (H0 Hz). split; [intros H; left; exact H | intros [H|[H _]]; [exact H | exfalso; exact (H Hz)]].
    - destruct (H1 Hz) as (Hd1 & Htg). split; intros _; [right; split; [exact Hz|] | exact Hd1].
      intros Heq. apply Htg. rewrite Heq. apply exvc_tag_mk. }
  exw_run_to (RUNTO (e_mem E)) HS HJ SHOK HPM EXVC_DEC.
  { exvc_awr U9 U19. }
  exw_kept_of HFr (fun _ : Z => False) ltac:(fun h => idtac).
  rename KEPT into K2. rename HG into G2. clear HF HFr.
  pose proof (regs_kept_of_st_ok rsegs _ _ _ regs _ [2; 3; 4; 8; 9; 18; 19; 24; 25; 26]%bv HS AGE
    ltac:(vm_compute; reflexivity)) as RK.
  prreg HS (13%bv : bv 5) R13'. rewrite U19 in R13'.
  lazymatch type of HS with st_ok _ _ _ (restrict _ ?mx) =>
    assert (KA : forall a, 0 <= a < 2 ^ 64 -> aview rsegs (w_H Wc) (ms_mem mx) a = aview rsegs (w_H Wc) memc a)
      by (intros a Ha; rewrite K2, K1 by (first [assumption | tauto]); reflexivity);
    assert (GA : forall a, apresent (w_H Wc) memc a -> apresent (w_H Wc) (ms_mem mx) a)
      by (intros a Ha; apply (apresent_grows _ _ _ a G2), (apresent_grows _ _ _ a G1), Ha) end.
  pmkst HS.
  eapply (exvc_tail n HX E lyc Sc Hpc Wc _ _ _ k pos (PjGrammar.mk (c =? 123) (rev acc)) ip dlc Hn HP).
  + apply (KT E lyc Sc Hpc Wc regs memc mdc k pos _ _ _ k HP HB HJ); [| exact GA | exact HPM | exact RK].
    intros a Ha _ _. apply KA; exact Ha.
  + exact Hd32.
  + split; [|split; [|split; [|split]]].
    * apply (exw_val_kept rsegs (w_H Wc) memc); [|exact CP]. intros x Hx. apply KA; lia.
    * apply (exw_val_kept rsegs (w_H Wc) memc); [|exact CE]. intros x Hx. apply KA; lia.
    * apply (exw_val_kept rsegs (w_H Wc) memc); [|exact CD]. intros x Hx. apply KA; lia.
    * apply (exw_val_kept rsegs (w_H Wc) memc); [|exact CS]. intros x Hx. apply KA; lia.
    * apply (exw_val_kept rsegs (w_H Wc) memc); [|exact CL]. intros x Hx. apply KA; lia.
  + exact Hip.
  + exact Hdlc.
  + exact HV.
  + exact Hres.
  + exact R13'.
  + apply (exw_val_kept rsegs (w_H Wc) memc); [|exact SP104]. intros x Hx. apply KA; lia.
- (* vv <> 0: vv is the caller's tree, of the container's tag *)
  rewrite branch_eq_U in Hc. apply Z.eqb_neq in Hc. rewrite (U_atom Ev 32 vv E32), U_lit in Hc by lia.
  destruct HDIF as [(Hz & _ & _) | (Hvv & Hv0 & Htag & Hiff)]; [exfalso; exact (Hc Hz)|].
  subst vv.
  exw_run_to (RUNTO (e_mem E)) HS HJ SHOK HPM EXVC_CMP.
  { exvc_awr U9 U19. }
  exw_kept_of HFr (fun _ : Z => False) ltac:(fun h => idtac).
  rename KEPT into K2. rename HG into G2. clear HF HFr.
  pose proof (regs_kept_of_st_ok rsegs _ _ _ regs _ [2; 3; 4; 8; 9; 18; 19; 24; 25; 26]%bv HS AGE
    ltac:(vm_compute; reflexivity)) as RK.
  pose proof (regs_kept_of_st_ok rsegs _ _ _ regs _ [11]%bv HS AGE ltac:(vm_compute; reflexivity)
    11%bv (or_introl eq_refl)) as RK11.
  prreg HS (13%bv : bv 5) R13'. rewrite U19 in R13'.
  prreg HS (10%bv : bv 5) R10'.
  lazymatch type of HS with st_ok _ _ _ (restrict _ ?mx) =>
    assert (KA : forall a, 0 <= a < 2 ^ 64 -> aview rsegs (w_H Wc) (ms_mem mx) a = aview rsegs (w_H Wc) memc a)
      by (intros a Ha; rewrite K2, K1 by (first [assumption | tauto]); reflexivity);
    assert (GA : forall a, apresent (w_H Wc) memc a -> apresent (w_H Wc) (ms_mem mx) a)
      by (intros a Ha; apply (apresent_grows _ _ _ a G2), (apresent_grows _ _ _ a G1), Ha) end.
  pmkst HS.
  eapply (exvc_cmp n HX E lyc Sc Hpc Wc _ _ _ k pos (c =? 123) acc ip dlc Hn HP).
  + apply (KT E lyc Sc Hpc Wc regs memc mdc k pos _ _ _ k HP HB HJ); [| exact GA | exact HPM | exact RK].
    intros a Ha _ _. apply KA; exact Ha.
  + exact Hd32.
  + split; [|split; [|split; [|split]]].
    * apply (exw_val_kept rsegs (w_H Wc) memc); [|exact CP]. intros x Hx. apply KA; lia.
    * apply (exw_val_kept rsegs (w_H Wc) memc); [|exact CE]. intros x Hx. apply KA; lia.
    * apply (exw_val_kept rsegs (w_H Wc) memc); [|exact CD]. intros x Hx. apply KA; lia.
    * apply (exw_val_kept rsegs (w_H Wc) memc); [|exact CS]. intros x Hx. apply KA; lia.
    * apply (exw_val_kept rsegs (w_H Wc) memc); [|exact CL]. intros x Hx. apply KA; lia.
  + exact Hip.
  + exact Hdlc.
  + exact HV.
  + exact Hv0.
  + exact Htag.
  + exact Hiff.
  + rewrite R10'. rewrite E32. reflexivity.
  + cbn [ms_regs restrict] in RK11. rewrite RK11. exact R11.
  + exact R13'.
  + apply (exw_val_kept rsegs (w_H Wc) memc); [|exact SP104]. intros x Hx. apply KA; lia.
Qed.
End w.

(* ---- the segment lemma: ExvB_Top.v's seg_close at EXV_HYP ---- *)
Lemma exvB_close : forall {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive} B ARx SK,
  EXV_HYP B ARx SK ->
  forall n, (forall fx : YK11.FPState, CUT_CX (fx := fx) B ARx SK n) ->
  forall fx : YK11.FPState, CUT_CC (fx := fx) B ARx SK n.
Proof.
intros rc ci cp RL B ARx SK HYP n HX fx. exact (exvc_close (fx := fx) B ARx SK HYP n HX).
Qed.
Print Assumptions exvB_close.
