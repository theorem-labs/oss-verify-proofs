(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Rests on the tex_word_specX (kit 4f18c75d4900, PRH_FnEx ff16e926fb9e) through the Section premise EHW,
   discharged in ExvB_Disp.v by a Theorem Labs lane's PROVED ExwB.ex_word_holds_B; memnorm is carried as EXB's keep from the entry
   memory (YSRrMemnorm.v's design), not taken as a law. *)
(* Theorem Labs, 2026-10: fuzz_preset, image B (asan-ubsan, rebuilt pin f8f98a95bc52, unstripped twin 3b5e1a099b53),
   ex_value, segment C1 DISP, the WORD ARM (lane ExvDisp, piece EXVD_WORD of ExvB_Disp_arms.v): from B 0x83958
   (exv_pc 0x42c), where the dispatch has put a0 = in, a1 = the literal, a2 = its type, to the exit cut CUT_CX at
   B 0x83fa8 (exv_pc 0xa7c). Proves no function: the arm lemma `exvd_word_holds`.
   THE CODE (neutral listing, the internal file ex_value.fuzz_preset.asan-ubsan.s, a Theorem Labs lane's listing of the B' pin, rows 269-272):
   `ld a3, 152(s1)` (v, the spill slot), `jal ex_word` (PCall AS_ex_word, return to B 0x83960), `mv s5, a0`,
   `j 0x83fa8`. No UBSan check and no ASan check lie in the arm (the load is from ex_value's own frame).
   THE PROOF: one engine run (YC1fPx paj_run_x_inv over YCbqG's ajournal_x, carrying P m := memnorm (e_mem E) ->
   memnorm m, YSRrMemnorm.srr_inv_laws_imp) to the call; the call by YCbqGcallW.v's aj_call_xW_sp in the caller-window
   form at e1 = exv_sp E + e_d E - exv_s1 E with the tex_word_specX (premise EHW; its fpostWm keeps memnorm, its Q
   keeps S' = S, its fpre asks raZ < alloc_ceiling: the jal's return pc, a listing literal); EXB after the call from
   the PROVED call kit (ExvB_Loop_kitP.v exv_kit_call, KIT_EXB_CALL, at fx2 := fx: ex_word keeps the float
   state; room by exv_room_eq from S' = S), then one engine run (paj_run_to_x_inv) to the cut and ExvB_Open_kt.v's exv_kt;
   the functional post EXV_RES from ex_word's post, exvd_V_at / exvd_V_lit / exvd_prefixb_iff (the literal's tag
   decides the differs flag: PjTree.tag of null / false / true is 0 / 1 / 2, the literal's ty).
   Premises of the call: the literal is a C string of read-only image bytes (ExvB_Loop_kitQ.v exv_kit_rodata's
   image view at non-owned read-only bytes with EXV_HYP's eh_lit_own; the frame chain from exv_kit_chain; the bytes
   by computation against PjGrammar.w_true / w_false / w_null), its shadow from EXV_HYP's MARKED eh_litsh at the call
   state; v's header, alignment, shadow, range (0 <= v, v + 4 <= 2 ^ 47) and its distance from the callee's window
   from prhex_tree (pj_nodeR's pj_hdrR, exv_foot_rng) and EXV_PRE's footprint clause.
   Rule 24: proves no function (kind: segment lemma).
   Numerals: 0x42c, 0x434, 0xa7c (DERIVED: B 0x83958 / 0x83960 / 0x83fa8 minus ex_value's entry B 0x8352c,
   the internal file neutral_dis.py on the rebuilt image); 152, 160 (LENGTH: the spill slot of v and its end, B 0x83958); 8, 32, 36,
   40 (LENGTH: struct ex fields in->end, in->differs and its end, the struct); 4, 56 (LENGTH: v->type, a tree node);
   288, 319 (LENGTH: ex_value's frame and its 32-alignment slack, exv_s1_le); 64 (LENGTH: the fpre's stack margin);
   16 (LENGTH: stack alignment); 8, 16, 2 ^ 30 (LENGTH: a granule, the literal span bound); 4096, 2 ^ 32, 2 ^ 40,
   2 ^ 46, 2 ^ 47, 2 ^ 64, 256 (LENGTH: address-space, code-offset and byte bounds; 2 ^ 46 the return pc's bound
   below alloc_ceiling); 33, 37 (DERIVED: the symbolic engine's
   numbering - 33 the first havoc atom after the call, 37 its a0); register numbers 1-4, 8-13, 18-26 (WORD); 3 * 2 ^ 20
   (LENGTH: EXV_PRE's text bound). No ADDRESS: the literal addresses are exvd_lit's (B_prog_val (A_OBJ 2) + off). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YCbqG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YImgTop YGcfNames.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YCbqGcallW.
From OSSVerify.omx_clap_core.fuzz_preset.images Require AsanUbsan.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_FnEx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_Reader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import PRH_ImgB Img0 Listing_prog PAImg_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm YSRrMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import ExvB_Stmt ExvB_Disp_arms ExvB_Open_kt.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import ExvB_Loop_kit ExvB_Loop_kitP ExvB_Loop_kitQ.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

#[local] Existing Instance prh_img_B.

(* ---- the arm's symbolic entry state: every register its own atom (sr_atoms), atom 32 = v, the one region the
   spill slot 152(s1) read only ---- *)
Definition EXW_EV0 : Z := B_prog_sigma AS_ex_value - B_prog_base.
Definition ss_w : sstate :=
  mkSS (EXW_EV0 + 0x42c) sr_atoms
    [ YP09.mkRegion (Some 9%nat) 152 160 0 0 [YP09.mkChunk 152 (CVal 8 (SOff 32 0))] ]
    None (mkFacts [] [] []).
Definition exw_Bx : sv := SLit 0.
Definition exw_Bspan : Z * Z := (0, 0).
Definition exw_SH : list shent := [].

Ltac exw_in := cbn [In]; repeat (first [left; reflexivity | right]).

(* ---- pure facts ---- *)
Lemma exw_frame_ro : forall E (rs : smem) (m m' : word -> option byte),
  frame_of E rs m m' -> forallb (fun r => YP09.r_whi r <=? YP09.r_wlo r) rs = true -> forall x, m' x = m x.
Proof.
intros E rs m m' HF Hro x. apply HF. intros (r & Hin & Hr). rewrite forallb_forall in Hro.
pose proof (Hro r Hin) as Hr'. apply Z.leb_le in Hr'. lia.
Qed.
Lemma exw_av_pt : forall (H : word -> bool) (m m' : word -> option byte), (forall x, m' x = m x) ->
  forall a, aview rsegs H m' a = aview rsegs H m a.
Proof. intros H m m' E a. apply aview_eq_of. unfold mrestrict. rewrite E. reflexivity. Qed.
Lemma exw_pres_pt : forall (H : word -> bool) (m m' : word -> option byte), (forall x, m' x = m x) ->
  forall a, apresent H m a -> apresent H m' a.
Proof. intros H m m' E a Ha. unfold apresent in *. rewrite E. exact Ha. Qed.
Lemma exw_vm_av : forall (H H' : word -> bool) (m m' : word -> option byte) a n v,
  (forall i, (i < n)%nat -> aview rsegs H' m' (a + Z.of_nat i) = aview rsegs H m (a + Z.of_nat i)) ->
  val_mem rsegs (mrestrict H m) a n v -> val_mem rsegs (mrestrict H' m') a n v.
Proof. intros H H' m m' a n v E Hv k Hk. rewrite (mbyte_of_aview rsegs H H' m m' _ (E k Hk)). exact (Hv k Hk). Qed.
Lemma exw_vm1_of_aview : forall (H : word -> bool) (mem : word -> option byte) a b,
  aview rsegs H mem a = Some b -> 0 <= b < 256 -> val_mem rsegs (mrestrict H mem) a 1 b.
Proof.
intros H mem a b E Hb k Hk. assert (k = 0%nat) by lia. subst k. cbn [Z.of_nat]. rewrite Z.add_0_r.
unfold aview in E. destruct (mbyte rsegs (mrestrict H mem) a) as [x|] eqn:Ex; cbn [option_map] in E; [|discriminate E].
injection E as E. f_equal. apply bv_eq. rewrite E, Z_to_bv_unsigned. unfold bv_wrap, YO0f.le_byte.
change (bv_modulus 8) with 256. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
rewrite Z.shiftr_0_r. change (2 ^ 8) with 256. rewrite !Z.mod_small by lia. reflexivity.
Qed.

(* the callee footprint of ex_word lies in ex_value's *)
Lemma exw_fp1 : forall q a, inFP [(q, q + 8); (q + 32, q + 36)] a -> (q <= a < q + 8) \/ (q + 32 <= a < q + 36).
Proof. intros q a (r & Hr & H). destruct Hr as [<- | [<- | []]]; cbn [fst snd] in H; [left|right]; exact H. Qed.
Lemma exw_fp1_sub : forall X a, inFP [(e_q X, e_q X + 8); (e_q X + 32, e_q X + 36)] a -> inFP (exv_FP X) a.
Proof.
intros X a H. destruct (exw_fp1 _ _ H) as [Ha|Ha]; unfold exv_FP, inFP.
- exists (e_q X, e_q X + 8). split; [right; left; reflexivity | exact Ha].
- exists (e_q X + 32, e_q X + 36). split; [right; right; right; left; reflexivity | exact Ha].
Qed.

(* the registers the cuts keep *)
Lemma exw_sub : forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 24; 25; 26]%bv ->
  In r [2; 3; 4; 8; 9; 10; 11; 12; 18; 19; 24; 25; 26]%bv.
Proof. intros r Hr. cbn [In] in Hr |- *. tauto. Qed.
Lemma exw_cs : forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 24; 25; 26]%bv -> acallee_saved (bv_unsigned r).
Proof.
intros r Hr. cbn [In] in Hr. unfold acallee_saved.
repeat (destruct Hr as [<- | Hr];
  [lazymatch goal with |- context [bv_unsigned ?b] =>
     let z := eval vm_compute in (bv_unsigned b) in replace (bv_unsigned b) with z by reflexivity end; lia |]).
destruct Hr.
Qed.

(* a tree node's header (PRH_Reader.pj_nodeR, every arm) *)
Lemma exw_node_hdr : forall m lblk p t D, PRH_Reader.pj_nodeR rsegs m lblk p t D ->
  exists num str kids keys n cap, PRH_Reader.pj_hdrR rsegs m p (PjTree.tag t) num str kids keys n cap.
Proof.
intros m lblk p t D H.
destruct t; cbn [PRH_Reader.pj_nodeR] in H; destruct H as (_ & _ & num & str & kids & keys & n & cap & Hh & _);
  exists num, str, kids, keys, n, cap; exact Hh.
Qed.

(* ex_word's stack need fits under ex_value's, with the 32-alignment slack *)
Lemma exw_stk : forall n, 0 <= @STK_ex_word prh_img_B /\ @STK_ex_word prh_img_B + 319 <= @STK_ex_value prh_img_B n.
Proof.
intros n.
assert (H1 : (@STK_ex_word prh_img_B + 319 <=? @STK_ex_value prh_img_B 0) = true) by (vm_compute; reflexivity).
assert (H2 : (0 <=? @STK_ex_word prh_img_B) = true) by (vm_compute; reflexivity).
apply Z.leb_le in H1, H2. split; [exact H2|].
assert (H3 : @STK_ex_value prh_img_B 0 <= @STK_ex_value prh_img_B n).
{ unfold STK_ex_value. pose proof (@pi_frame_nonneg prh_img_B F_ex_value) as H4. nia. }
lia.
Qed.

(* the literals: read-only image bytes of the first (read-only) segment, word-aligned, then NULs to the granule end *)
Definition exw_seg : Segment := nth 0 rsegs AsanUbsan.AsanUbsan_segment_000.
Definition exw_romb (a : Z) : option Z := option_map (fun b : byte => bv_unsigned b) (YK11.seg_rom rsegs (Z_to_bv 64 a)).
Lemma exw_seg_ro : In exw_seg rsegs /\ seg_writable exw_seg = false.
Proof. split; [apply nth_In; vm_compute; lia | vm_compute; reflexivity]. Qed.
Lemma exw_lit : forall c w ty wl u, exvd_lit c w ty wl u ->
  4096 <= w /\ w + 16 <= 2 ^ 30 /\ w mod 8 = 0 /\ (4 <= length wl <= 5)%nat /\ Forall (fun b => 0 < b < 256) wl /\
  Z.of_N (seg_base exw_seg) <= w /\ w + 8 <= Z.of_N (seg_base exw_seg) + Z.of_N (seg_size exw_seg) /\
  (forall j, (j < 8)%nat -> exw_romb (w + Z.of_nat j) = Some (nth j (wl ++ [0; 0; 0; 0]) 0)) /\
  0 <= ty <= 2 /\ (forall t, PjTree.tag t = ty <-> t = u).
Proof.
intros c w ty wl u H.
destruct H as [(-> & -> & -> & -> & ->) | [(-> & -> & -> & -> & ->) | (-> & -> & -> & -> & ->)]].
all: split; [apply Z.leb_le; vm_compute; reflexivity|].
all: split; [apply Z.leb_le; vm_compute; reflexivity|].
all: split; [apply Z.eqb_eq; vm_compute; reflexivity|].
all: split; [cbn; lia|].
all: split; [apply Forall_forall; intros b Hb; cbn in Hb; repeat (destruct Hb as [<-|Hb]; [lia|]); destruct Hb|].
all: split; [apply Z.leb_le; vm_compute; reflexivity|].
all: split; [apply Z.leb_le; vm_compute; reflexivity|].
all: split; [intros j Hj; do 8 (destruct j as [|j]; [vm_compute; reflexivity|]); lia|].
all: split; [lia|].
all: intros t; destruct t; cbn [PjTree.tag]; split; intros Ht; first [reflexivity | discriminate | lia].
Qed.

(* the grammar at the literal's first byte *)
Lemma exw_V : forall X c w ty wl u, e_i0 X <= exv_len X -> exv_i1 X < exv_len X ->
  nth (Z.to_nat (exv_i1 X)) (e_x X) 0 = c -> exvd_lit c w ty wl u ->
  exv_V X = if PjGrammar.prefixb wl (skipn (Z.to_nat (exv_i1 X)) (e_x X))
            then Some (u, skipn (length wl) (skipn (Z.to_nat (exv_i1 X)) (e_x X))) else None.
Proof.
intros X c w ty wl u Hi0 Hi1 Hc HL.
assert (Hlt : (Z.to_nat (exv_i1 X) < length (e_x X))%nat)
  by (pose proof (exvd_i1_range X); unfold exv_len in *; zl).
rewrite (exvd_V_at X Hi0 Hi1), Hc, (exvd_V_lit (e_dep X) c w ty wl u _ HL).
rewrite (exvd_skipn_nth (e_x X) (Z.to_nat (exv_i1 X)) Hlt), Hc. reflexivity.
Qed.
Lemma exw_hit : forall wl (x : list Z) i, 0 <= i <= Z.of_nat (length x) ->
  (Z.of_nat (length wl) <= Z.of_nat (length x) - i /\ firstn (length wl) (skipn (Z.to_nat i) x) = wl) <->
  PjGrammar.prefixb wl (skipn (Z.to_nat i) x) = true.
Proof.
intros wl x i Hi. rewrite exvd_prefixb_iff, length_skipn.
split; intros (H1 & H2); (split; [lia | exact H2]).
Qed.

(* YC1fP's prreg at image B's instance, passed explicitly (ExvB_Exit.v's exx_reg) *)
Ltac exw_reg HS r Hr :=
  lazymatch type of HS with
  | st_ok_pi _ _ ?E ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_pi_restrict_reg (L := B_prog_listing) (PI := PI_prog_B) H E ss ms r HS) as Hr;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
    cbn [ms_regs restrict mkst] in Hr; prreg_norm Hr
  end.

Section s. Context {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
#[local] Notation VAL := (@pa_val _ B_prog_listing PI_prog_B).
#[local] Notation BASE := (@pa_val _ B_prog_listing PI_prog_B A_TEXT).
#[local] Notation PST := (@prh_pst prh_img_B).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world rsegs -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
Hypothesis HYP : EXV_HYP B ARx SK.
(* ex_word's text: the tex_word_specX (kit 4f18c75d4900, PRH_FnEx ff16e926fb9e); discharged in ExvB_Disp.v by
   a Theorem Labs lane's PROVED ExwB.ex_word_holds_B *)
Hypothesis EHW : forall fx : YK11.FPState,
  tex_word_specX (fx := fx) (PI := prh_img_B) (L := B_prog_listing) (PA := PI_prog_B) B ARx SK.

Section f. Context {fx : YK11.FPState}.

Lemma exw_pc : forall off, BASE + (EXW_EV0 + off) = exv_pc off.
Proof.
intros off. assert (HB : BASE = B_prog_base) by (vm_compute; reflexivity). unfold EXW_EV0, exv_pc. rewrite HB. lia.
Qed.
Lemma exw_ret : 0 <= EXW_EV0 + 0x434 < 2 ^ 40 /\ (EXW_EV0 + 0x434) mod 2 = 0 /\
  4096 <= BASE + (EXW_EV0 + 0x434) < 2 ^ 46.
Proof.
assert (H : ((0 <=? EXW_EV0 + 0x434) && (EXW_EV0 + 0x434 <? 2 ^ 40) && ((EXW_EV0 + 0x434) mod 2 =? 0) &&
  (4096 <=? BASE + (EXW_EV0 + 0x434)) && (BASE + (EXW_EV0 + 0x434) <? 2 ^ 46)) = true) by (vm_compute; reflexivity).
rewrite !andb_true_iff, !Z.leb_le, !Z.ltb_lt, !Z.eqb_eq in H. lia.
Qed.

Definition exw_E (regs : bvmap 5 word) (v : Z) : env := @Eimg _ B_prog_listing PI_prog_B (Ereg regs [w64 v]).
Lemma exw_E_low : forall regs v n, (n < A_TEXT)%nat -> ew (exw_E regs v) n = ew (Ereg regs [w64 v]) n.
Proof. intros regs v n Hn. unfold exw_E. apply Eimg_low. exact Hn. Qed.
Lemma exw_E_reg : forall regs v (r : bv 5) n, Z.of_nat n = bv_unsigned r -> ew (exw_E regs v) n = getr regs r.
Proof.
intros regs v r n Hn. pose proof (bv_unsigned_in_range 5 r) as R. change (bv_modulus 5) with 32 in R.
rewrite exw_E_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn.
Qed.
Lemma exw_E_v : forall regs v, ew (exw_E regs v) 32 = w64 v.
Proof. intros. rewrite exw_E_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 0). Qed.
Lemma exw_E_agree : forall regs v, env_agree 32 (Ereg regs [w64 v]) (exw_E regs v).
Proof. intros. split; [intros n Hn; apply exw_E_low; unfold A_TEXT; lia | reflexivity]. Qed.

(* ---- the entry symbolic state ---- *)
Lemma exw_entry : forall (W : world rsegs) (regs : bvmap 5 word) (mem : word -> option byte) (s1 v : Z),
  getr regs 9 = w64 s1 -> 0 <= s1 -> s1 + 160 <= 2 ^ 64 -> 0 <= v < 2 ^ 64 ->
  val_mem rsegs (rdW W mem) (s1 + 152) 8 v ->
  st_ok_pi rsegs VAL (exw_E regs v) ss_w
    (restrict (w_H W) (YK11.mkst regs (Z_to_bv 64 (BASE + (EXW_EV0 + 0x42c))) mem (YK11.seg_rom rsegs)))
  /\ sh_ok rsegs exw_Bx exw_SH (exw_E regs v) (rdW W mem).
Proof.
intros W regs mem s1 v H9 Hs0 Hs1 Hv HM.
assert (U9 : bv_unsigned (ew (exw_E regs v) 9) = s1).
{ rewrite (exw_E_reg regs v 9%bv 9) by reflexivity. rewrite H9. unfold w64. apply unsigned_lit_small. lia. }
rewrite restrict_mkst_fx. split.
- unfold ss_w. apply (pa_entry_st_ok_full (fx := fx) (L := B_prog_listing) (PI := PI_prog_B)).
  + apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + apply Forall_cons; [|apply Forall_nil].
    unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val rsegs _ _ s1 152 8 (SOff 32 0) v).
    * cbn [sv_denot]. rewrite exw_E_v. unfold w64. rewrite Z.add_0_r, unsigned_lit_small by lia. reflexivity.
    * change (8 * Z.of_N 8) with 64. lia.
    * cbn. lia.
    * exact HM.
  + cbn. split; exact I.
  + split; [exact I | split; exact I].
- unfold sh_ok, exw_SH. apply Forall_nil.
Qed.

(* ---- the literal is a C string ex_word may take (cstr_ok), at any state with the ROM view and its shadow ---- *)
Lemma exw_cstr : forall (W : world rsegs) mem c w ty wl u,
  exvd_lit c w ty wl u ->
  (forall a, in_rom rsegs a -> ~ Exists (in_zr a) (as_owned_static B) ->
     aview rsegs (w_H W) mem a = option_map (fun b : byte => bv_unsigned b) (seg_rom rsegs (Z_to_bv 64 a))) ->
  range_addressable (aview rsegs (w_H W) mem) SHADOW_OFF w (Z.of_nat (length wl) + 1) ->
  shadow_hull_vis (aview rsegs (w_H W) mem) w (Z.of_nat (length wl) + 1) ->
  cstr_ok (PA := PI_prog_B) W mem w wl.
Proof.
intros W mem c w ty wl u HL HROM HRA HHV.
destruct (exw_lit c w ty wl u HL) as (H4096 & H30 & H8 & Hlen & HF & Hlo & Hhi & HB & _).
destruct exw_seg_ro as (Hsin & Hsro).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
(* the string and its NUL: non-owned read-only bytes, read through the image view *)
assert (AV : forall j, (j <= length wl)%nat -> aview rsegs (w_H W) mem (w + Z.of_nat j) = Some (nth j (wl ++ [0; 0; 0; 0]) 0)).
{ intros j Hj. rewrite HROM; [exact (HB j ltac:(lia))| |].
  - exists exw_seg. split; [exact Hsin|]. split; [exact Hsro|]. lia.
  - apply (eh_lit_own B ARx SK HYP c w ty wl u HL). lia. }
(* every byte of the granule is visible: an in-segment byte reads the overlay or the image, never None *)
assert (NN : forall j, (j < 8)%nat -> aview rsegs (w_H W) mem (w + Z.of_nat j) <> None).
{ intros j Hj. pose proof (HB j Hj) as Hb. unfold exw_romb in Hb.
  unfold aview, mbyte. destruct (mrestrict (w_H W) mem (Z_to_bv 64 (w + Z.of_nat j))); [discriminate|].
  intros Hn.
  assert (E0 : option_map (fun b : byte => bv_unsigned b) (YK11.seg_rom rsegs (Z_to_bv 64 (w + Z.of_nat j))) = None)
    by exact Hn.
  rewrite E0 in Hb. discriminate Hb. }
split; [split|].
- intros j Hj. rewrite length_app in Hj. cbn [length] in Hj.
  assert (Ej : nth j (wl ++ [0]) 0 = nth j (wl ++ [0; 0; 0; 0]) 0).
  { replace (wl ++ [0; 0; 0; 0]) with ((wl ++ [0]) ++ [0; 0; 0]) by (rewrite <- app_assoc; reflexivity).
    assert (Hj' : (j < length (wl ++ [0%Z]))%nat) by (rewrite length_app; cbn [length]; lia).
    rewrite (app_nth1 (wl ++ [0]) [0; 0; 0] 0 Hj'). reflexivity. }
  assert (Hb : 0 <= nth j (wl ++ [0]) 0 < 256).
  { destruct (Nat.lt_ge_cases j (length wl)) as [Hl|Hl].
    - rewrite app_nth1 by exact Hl. rewrite Forall_forall in HF. pose proof (HF (nth j wl 0) (nth_In wl 0 Hl)). lia.
    - rewrite app_nth2 by exact Hl. replace (j - length wl)%nat with 0%nat by lia. cbn. lia. }
  split; [|exact Hb].
  apply exw_vm1_of_aview; [|exact Hb]. rewrite Ej. apply AV. lia.
- revert HF. apply Forall_impl. intros b Hb. lia.
- split; [lia|]. split; [lia|]. split; [lia|]. split; [unfold amem_range; left; lia|].
  split; [exact HRA|]. split; [exact HHV|].
  intros a Ha.
  assert (Hj : (Z.to_nat (a - w) < 8)%nat) by lia.
  pose proof (NN _ Hj) as Ha'. replace (w + Z.of_nat (Z.to_nat (a - w))) with a in Ha' by lia.
  exact Ha'.
Qed.

(* ---- THE ARM ---- *)
Lemma exw_at : forall n, (forall fx' : YK11.FPState, CUT_CX (fx := fx') B ARx SK n) -> EXVD_WORD (fx := fx) B ARx SK n.
Proof.
intros n HCX. unfold EXVD_WORD.
intros X lyc Sc Hpc Wc regs memc mdc k pos c w ty wl u Hn HPRE HEXB HCUR Hi1 Hnth HLIT H10 H11 H12 HSP.
pose proof (eh_laws B ARx SK HYP) as LAWS.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HPRE as HP. unfold EXV_PRE in HP. cbv zeta in HP.
destruct HP as ((HFN & _ & HHI0) & HPfrm & HPcnt & HP10 & HP11 & HPcur & HPq8 & HPch & HPq1 & HPq2 & HPwin & HPsrc
  & HPblk & HPlen & HPi0 & HPdep & HPdn & HPdl & HPwd & HPscr & HPd1 & HPd2 & HPv & HPled).
pose proof HFN as (HAR0 & _ & _ & _ & _ & Hastk0 & _ & _ & _).
destruct Hastk0 as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _ & Htop1 & Htop2).
destruct HPwin as (Hd0 & Hd16 & Hdtop & _).
pose proof HEXB as HB0. unfold EXB in HB0. cbv zeta in HB0.
destruct HB0 as (HJ & _ & HFK & HFZ & _ & _ & HRM0 & HLED & _ & R2 & R8 & R9 & _ & _ & _ & _ & R19 & R3 & R4 & _ & _ & _
  & _ & _ & _ & _ & _ & HTREE).
pose proof (exv_s1_le X) as ((S1a & S1b) & S1m).
pose proof (exw_stk (e_n X)) as (Hw0 & Hw1).
pose proof (exvd_i1_range X) as Hi1r.
assert (SP : exv_sp X = spZ (e_regs X)) by reflexivity.
assert (ESTK : exv_STK X = @STK_ex_value prh_img_B (e_n X)) by reflexivity.
assert (EL : exv_len X = Z.of_nat (length (e_x X))) by reflexivity.
assert (Hv64 : 0 <= e_v X < 2 ^ 64).
{ destruct HTREE as [Hv0 | (Hnd & Hhome & _)]; [rewrite Hv0; lia|].
  pose proof HJ as (HARc & Hly & _).
  destruct Hly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ehi & _).
  assert (Hhi : ly_stk_hi lyc <= 2 ^ 47) by lia.
  pose proof (exv_foot_rng B ARx SK HYP lyc Sc Hpc Wc memc mdc (e_Lam X) (e_peak X) (e_cnt X) (e_fail X) (e_ran X) (e_most X) (e_own X)
    regs (e_v X) (e_t X) (e_D X) HARc HLED Hnd Hhome Hhi (e_v X) ltac:(left; lia)). lia. }
(* The range premise of the tag pointer: 0 <= v and v + 4 <= 2 ^ 47 (v = 0, or the node's footprint, exv_foot_rng at
   v and v + 3) *)
assert (HVR : 0 <= e_v X /\ e_v X + 4 <= 2 ^ 47).
{ destruct HTREE as [Hv | (Hnd & Hhome & _)]; [rewrite Hv; lia|].
  pose proof HJ as (HARc & Hly & _).
  destruct Hly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ehi & _).
  assert (Hhi : ly_stk_hi lyc <= 2 ^ 47) by lia.
  pose proof (exv_foot_rng B ARx SK HYP lyc Sc Hpc Wc memc mdc (e_Lam X) (e_peak X) (e_cnt X) (e_fail X) (e_ran X) (e_most X) (e_own X)
    regs (e_v X) (e_t X) (e_D X) HARc HLED Hnd Hhome Hhi (e_v X) ltac:(left; lia)) as F0.
  pose proof (exv_foot_rng B ARx SK HYP lyc Sc Hpc Wc memc mdc (e_Lam X) (e_peak X) (e_cnt X) (e_fail X) (e_ran X) (e_most X) (e_own X)
    regs (e_v X) (e_t X) (e_D X) HARc HLED Hnd Hhome Hhi (e_v X + 3) ltac:(left; lia)) as F3.
  lia. }
(* ---- the run to the call ---- *)
destruct (exw_entry Wc regs memc (exv_s1 X) (e_v X) R9 ltac:(zl) ltac:(zl) Hv64 HSP) as [HS SHOK].
pose proof (exw_E_agree regs (e_v X)) as HAE.
pose proof (exw_E_v regs (e_v X)) as E0v.
assert (HEI : img_env VAL A_LIM (exw_E regs (e_v X))) by (unfold exw_E; apply Eimg_env).
remember (exw_E regs (e_v X)) as E0 eqn:HE0. clear HE0.
(* memnorm carried from the entry memory (YSRrMemnorm.v): P at the cut's memory is EXB's keep *)
pose (P := fun m : word -> option byte => YAkMemnorm.memnorm rsegs (e_mem X) -> YAkMemnorm.memnorm rsegs m).
assert (PLAW : srr_inv_laws rsegs P)
  by exact (YSRrMemnorm.srr_inv_laws_imp rsegs (YAkMemnorm.memnorm rsegs) (e_mem X)
              (YSRrMemnorm.srr_inv_laws_memnorm_k rsegs)).
assert (HPM : P memc) by exact (proj2 HRM0).
pose (RUN := paj_run_x_inv (SK := SK) (PL := PL_prog_B) (PI := PI_prog_B) B PST ARx LAWS P PLAW).
pose (RUNTO := paj_run_to_x_inv (SK := SK) (PL := PL_prog_B) (PI := PI_prog_B) B PST ARx LAWS P PLAW).
unfold cfg_at. rewrite <- (exw_pc 0x42c). unfold w64 at 1.
paj_run_tok_x_inv RUN HS HJ SHOK HPM exw_Bspan.
{ unfold ss_w. cbn [ss_mem]. apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]. }
rename ms into ms1. rename HS into HS1. rename HJ into HJ1. rename HF into HF1. rename HFr into HFr1.
rename HG into HG1. rename SHOK into SHOK1. rename HPM into HPM1.
assert (EM : forall x, ms_mem ms1 x = memc x) by exact (exw_frame_ro _ _ _ _ HF1 ltac:(vm_compute; reflexivity)).
assert (RK : forall r, In r [2; 3; 4; 8; 9; 10; 11; 12; 18; 19; 24; 25; 26]%bv -> getr (ms_regs ms1) r = getr regs r)
  by exact (regs_kept_of_st_ok rsegs E0 _ _ regs [w64 (e_v X)] [2; 3; 4; 8; 9; 10; 11; 12; 18; 19; 24; 25; 26]%bv
              HS1 HAE ltac:(vm_compute; reflexivity)).
prreg HS1 (1%bv : bv 5) Rra. prreg HS1 (13%bv : bv 5) Ra3. rewrite E0v in Ra3.
lazymatch type of Rra with _ = Z_to_bv 64 (_ + ?z) =>
  assert (Eret : z = EXW_EV0 + 0x434) by (vm_compute; reflexivity); rewrite Eret in Rra end.
pose proof exw_ret as (Hret1 & Hret2 & Hret3).
assert (SPms : spZ (ms_regs ms1) = exv_s1 X).
{ unfold spZ. rewrite (RK 2%bv ltac:(exw_in)), R2. unfold w64. apply unsigned_lit_small. zl. }
assert (S0ms : s0Z (ms_regs ms1) = exv_sp X).
{ unfold s0Z. rewrite (RK 8%bv ltac:(exw_in)), R8. unfold w64. apply unsigned_lit_small. zl. }
(* EXB at the call state (the run wrote nothing) *)
pose proof (exv_kt (fx := fx) B ARx SK HYP X lyc Sc Hpc Wc regs memc mdc k pos (ms_regs ms1) (ms_mem ms1) _ k
  HPRE HEXB HJ1 (fun a _ _ _ => exw_av_pt (w_H Wc) memc (ms_mem ms1) EM a)
  (fun a => exw_pres_pt (w_H Wc) memc (ms_mem ms1) EM a) HPM1 (fun r Hr => RK r (exw_sub r Hr))) as HEXB1.
pose proof HEXB1 as HB1. unfold EXB in HB1. cbv zeta in HB1.
destruct HB1 as (_ & _ & _ & _ & _ & _ & _ & HLED1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
  & HSRC1 & HTB1 & _ & _ & _ & HTREE1).
destruct (exv_kit_rodata B ARx SK HYP fx X lyc Sc Hpc Wc (ms_regs ms1) (ms_mem ms1) _ k pos HPRE HEXB1)
  as (HROD1 & HROM1).
destruct (exv_kit_chain B ARx SK fx X lyc Sc Hpc Wc (ms_regs ms1) (ms_mem ms1) _ k pos (ms_regs ms1) HPRE HEXB1
  ltac:(rewrite (RK 2%bv ltac:(exw_in)); exact R2) ltac:(rewrite (RK 8%bv ltac:(exw_in)); exact R8)) as (ch1 & Hch1 & _).
pose proof (proj1 HJ1) as HAR1. cbv beta in HAR1.
destruct (eh_litsh B ARx SK HYP _ _ _ _ _ _ HAR1 c w ty wl u HLIT) as (HRAw & HHVw).
pose proof (exw_cstr Wc (ms_mem ms1) c w ty wl u HLIT HROM1 HRAw HHVw) as HCSTR.
destruct (exw_lit c w ty wl u HLIT) as (_ & _ & _ & _ & _ & _ & _ & _ & Hty & Htag).
(* the cursor cells at the call state *)
assert (TM1 : forall a nn v, val_mem rsegs (rdW Wc memc) a nn v -> val_mem rsegs (rdW Wc (ms_mem ms1)) a nn v).
{ intros a nn v Hv. apply (exw_vm_av (w_H Wc) (w_H Wc) memc (ms_mem ms1) a nn v); [|exact Hv].
  intros i Hi. apply exw_av_pt. exact EM. }
pose proof HCUR as (Cq & Cq8 & Cq16 & Cq24 & Cq32).
(* v's header for ex_word's v->type read *)
assert (HVT : e_v X <> 0 ->
  val_mem rsegs (rdW Wc (ms_mem ms1)) (e_v X) 4 (PjTree.tag (e_t X)) /\ 0 <= PjTree.tag (e_t X) < 2 ^ 32 /\
  e_v X mod 8 = 0 /\ range_addressable (aview rsegs (w_H Wc) (ms_mem ms1)) SHADOW_OFF (e_v X) 4 /\
  (e_v X + 4 <= spZ (ms_regs ms1) - @STK_ex_word prh_img_B \/ spZ (ms_regs ms1) <= e_v X)).
{ intros Hv0.
  destruct HTREE1 as [Hv | (Hnd & _ & Hra & _)]; [contradiction|].
  destruct HPv as [Hv | (_ & _ & HDJ)]; [contradiction|].
  destruct (exw_node_hdr _ _ _ _ _ Hnd) as (num & str & kids & keys & nn & cap & (Hrw & Hty4 & _)).
  destruct Hrw as (Hal8 & _). destruct Hty4 as (Htr & Htv).
  split; [exact Htv|]. split; [exact Htr|]. split; [exact Hal8|].
  split; [intros x Hx; apply Hra; lia|].
  rewrite SPms.
  pose proof (HDJ (e_v X) ltac:(left; lia)) as (_ & _ & Hs & _).
  pose proof (HDJ (e_v X + 55) ltac:(left; lia)) as (_ & _ & Hs' & _).
  zl. }
(* ---- the call of ex_word ---- *)
eapply SRr_bind.
{ eapply (aj_call_xW_sp (SK := SK) rsegs B PST ARx LAWS B_prog_segs_low Wc E0 _ ms1
    (exv_STK X + e_d X) (exv_sp X + e_d X) (exv_FP X) (e_ly X) (e_S X) (e_Hp X) (e_W X) (e_mem X) (e_md X) [(1, pos)]
    lyc Sc Hpc _ k (@STK_ex_word prh_img_B) (exv_sp X + e_d X - exv_s1 X)
    [(e_q X, e_q X + 8); (e_q X + 32, e_q X + 36)] (exv_s1 X - (exv_sp X + e_d X))
    (Z_to_bv 64 (BASE + (EXW_EV0 + 0x434))) ch1 _ HS1 eq_refl HJ1).
  - rewrite SPms. lia.
  - zl.
  - zl.
  - exact Hw0.
  - zl.
  - zl.
  - zl.
  - zl.
  - rewrite (RK 3%bv ltac:(exw_in)). exact R3.
  - rewrite (RK 4%bv ltac:(exw_in)). exact R4.
  - exact Rra.
  - apply (ret_ok_codeptr_v (PI := PI_prog_B)); lia.
  - rewrite unsigned_lit_small by lia. lia.
  - rewrite S0ms. replace (exv_sp X + e_d X + (exv_s1 X - (exv_sp X + e_d X))) with (exv_s1 X) by lia. exact Hch1.
  - intros HPRE1 HWIN1.
    pose proof HPRE1 as (_ & _ & _ & _ & _ & (_ & _ & _ & _ & _ & _ & _ & _ & Htt1) & _).
    pose proof HWIN1 as (_ & _ & Hwt1 & _).
    assert (Hhi1 : spZ (ms_regs ms1) + 64 <= ly_stk_hi lyc) by (rewrite SPms in Hwt1 |- *; zl).
    assert (Hra1 : raZ (ms_regs ms1) < YM05.alloc_ceiling)
      by (unfold raZ; rewrite Rra, unsigned_lit_small by lia; lia).
    exact (EHW fx lyc Sc Hpc Wc (ms_regs ms1) (ms_mem ms1) _ ch1 (e_q X) w ty (e_v X)
      (PjTree.tag (e_t X)) (e_x0 X) (exv_i1 X) (exv_sp X + e_d X - exv_s1 X) wl (e_x X)
      (e_Lam X) (e_peak X) (e_cnt X) (e_fail X) (e_ran X) (e_most X) (e_own X)
      (conj HPRE1 (conj HROD1 (conj Hhi1 (conj Hra1 HFZ))))
      ltac:(rewrite (RK 10%bv ltac:(exw_in)); exact H10)
      ltac:(rewrite (RK 11%bv ltac:(exw_in)); exact H11)
      ltac:(rewrite (RK 12%bv ltac:(exw_in)); exact H12)
      Ra3 HCSTR Hty HVR (TM1 _ _ _ Cq) (TM1 _ _ _ Cq8) HPq8 ltac:(rewrite SPms; zl) ltac:(rewrite SPms; zl) HWIN1
      HSRC1 (HTB1 ltac:(zl)) HPlen Hi1r HVT HLED1).
  - intros a Ha. left. exact (exw_fp1_sub X a Ha). }
cbv beta. intros W2 c2 Hwle (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & Hc2 & HJ2 & HJc & HWIN2 & HP2 & HK2).
subst c2. cbv beta delta [fQmn] in HK2.
destruct HK2 as ((HRL2 & HHp2 & HSS2 & HAB2 & HLED2 & HRES2) & HMN2).
assert (Eo : exv_sp X + e_d X + (exv_s1 X - (exv_sp X + e_d X)) = exv_s1 X) by lia.
assert (Ee : exv_s1 X + (exv_sp X + e_d X - exv_s1 X) = exv_sp X + e_d X) by lia.
rewrite Eo, Ee in HJc. rewrite Eo, Ee in HWIN2.
(* ---- EXB after the call (the kit) ---- *)
assert (RK2 : forall r, In r [2; 3; 4; 8; 9; 18; 19; 24; 25; 26]%bv -> getr regs2 r = getr (ms_regs ms1) r).
{ intros r Hr. rewrite <- (Z_to_bv_bv_unsigned _ r). exact (HP2 _ (exw_cs r Hr)). }
destruct (exv_kit_call B ARx SK HYP fx X lyc Sc Hpc Wc (ms_regs ms1) (ms_mem ms1) _ k pos fx
  [(e_q X, e_q X + 8); (e_q X + 32, e_q X + 36)]
  (@STK_ex_word prh_img_B + (exv_sp X + e_d X - exv_s1 X)) ly2 S2 Hp2 W2 regs2 mem2 md2 k1 HPRE HEXB1
  (exw_fp1_sub X) HJ2 HJc HWIN2 RK2 ltac:(intros r _; reflexivity) HFZ
  (exv_room_eq Sc Sc S2 (exv_room_refl Sc) HSS2) (fun H => HMN2 (HPM1 H)) HHp2 HAB2 HLED2) as (HEXB2 & _).
(* ---- the run to the exit cut ---- *)
pose proof (st_ok_pi_after_call (L := B_prog_listing) (PI := PI_prog_B) 33%nat E0 _ (restrict (w_H Wc) ms1) regs2
  (mrestrict (w_H W2) mem2) [] (EXW_EV0 + 0x434) HEI ltac:(lia) HS1 eq_refl ltac:(cbv; lia)
  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
  ltac:(vm_compute; reflexivity) ltac:(submem_tac) ltac:(vm_compute; reflexivity) HP2 (Forall_nil _)) as HS2.
rewrite <- restrict_mkst_fx in HS2.
remember (havoc E0 33 (map (getr regs2) CLOB)) as E2 eqn:HE2 in HS2.
assert (HEI2 : img_env VAL A_LIM E2) by (rewrite HE2; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (E2a0 : ew E2 37 = getr regs2 10) by (rewrite HE2; reflexivity).
assert (HAE2 : env_agree 32 (Ereg regs [w64 (e_v X)]) E2) by (rewrite HE2; apply env_agree_havoc_ge; [lia | exact HAE]).
assert (SHOK2 : sh_ok rsegs exw_Bx exw_SH E2 (rdW W2 mem2)) by (unfold sh_ok, exw_SH; apply Forall_nil).
clear HE2.
assert (HPM2 : P mem2) by (unfold P; intros H; exact (HMN2 (HPM1 H))).
paj_run_to_tok_x_inv RUNTO HS2 HJ2 SHOK2 HPM2 exw_Bspan (EXW_EV0 + 0xa7c).
{ apply awr_ok_nil. }
assert (EM3 : forall x, ms_mem ms x = mem2 x) by exact (exw_frame_ro _ _ _ _ HF ltac:(vm_compute; reflexivity)).
exw_reg HS2 (21%bv : bv 5) R21. rewrite E2a0 in R21.
assert (RK3 : forall r, In r [2; 3; 4; 8; 9; 18; 19; 24; 25; 26]%bv -> getr (ms_regs ms) r = getr regs r)
  by exact (regs_kept_of_st_ok_pi (L := B_prog_listing) (PI := PI_prog_B) E2 _ _ regs [w64 (e_v X)]
              [2; 3; 4; 8; 9; 18; 19; 24; 25; 26]%bv HS2 HAE2 ltac:(vm_compute; reflexivity)).
pose proof (exv_kt (fx := fx) B ARx SK HYP X ly2 S2 Hp2 W2 regs2 mem2 md2 (k + k1) pos (ms_regs ms) (ms_mem ms) _ (k + k1)
  HPRE HEXB2 HJ2 (fun a _ _ _ => exw_av_pt (w_H W2) mem2 (ms_mem ms) EM3 a)
  (fun a => exw_pres_pt (w_H W2) mem2 (ms_mem ms) EM3 a) HPM2
  (fun r Hr => eq_trans (RK3 r Hr) (eq_sym (eq_trans (RK2 r Hr) (RK r (exw_sub r Hr)))))) as HEXB3.
rewrite (st_ok_pi_restrict_mkst (L := B_prog_listing) (PI := PI_prog_B) _ _ _ _ HS2 eq_refl). cbn [ss_pc].
lazymatch goal with |- context [Z_to_bv 64 (BASE + ?z)] =>
  replace (Z_to_bv 64 (BASE + z)) with (w64 (exv_pc 0xa7c)) by (unfold w64; f_equal; vm_compute; reflexivity) end.
(* the cursor cells after the call and the run *)
assert (TW : forall a nn v, val_mem rsegs (rdW Wc memc) a nn v -> e_q X + 8 <= a -> a + Z.of_nat nn <= e_q X + 32 ->
  val_mem rsegs (rdW W2 (ms_mem ms)) a nn v).
{ intros a nn v Hv H1 H2. apply (exw_vm_av (w_H Wc) (w_H W2) memc (ms_mem ms) a nn v); [|exact Hv].
  intros i Hi. rewrite (exw_av_pt _ _ _ EM3). rewrite HWIN2.
  - apply exw_av_pt. exact EM.
  - zl.
  - intros Hf. destruct (exw_fp1 _ _ Hf); zl. }
assert (TS : forall a nn v, val_mem rsegs (rdW Wc memc) a nn v ->
  prhex_same (PA := PI_prog_B) Wc (ms_mem ms1) W2 mem2 a (Z.of_nat nn) -> val_mem rsegs (rdW W2 (ms_mem ms)) a nn v).
{ intros a nn v Hv Hs. apply (exw_vm_av (w_H Wc) (w_H W2) memc (ms_mem ms) a nn v); [|exact Hv].
  intros i Hi. rewrite (exw_av_pt _ _ _ EM3), Hs by lia. apply exw_av_pt. exact EM. }
assert (TP : forall a nn v, val_mem rsegs (rdW W2 mem2) a nn v -> val_mem rsegs (rdW W2 (ms_mem ms)) a nn v).
{ intros a nn v Hv. apply (exw_vm_av (w_H W2) (w_H W2) mem2 (ms_mem ms) a nn v); [|exact Hv].
  intros i Hi. apply exw_av_pt. exact EM3. }
pose proof (exw_V X c w ty wl u (proj2 HPi0) Hi1 Hnth HLIT) as HV.
pose proof (exw_hit wl (e_x X) (exv_i1 X) Hi1r) as HH.
destruct HRES2 as [(Hhit & Ha0 & Hq & Hdf) | (Hmiss & Ha0 & Hsq & Hsd)].
- (* the word matched: r = 0, in->p past it *)
  pose proof (proj1 HH Hhit) as Hpre. pose proof Hhit as (Hhl & _).
  rewrite Hpre in HV.
  destruct Hdf as [(Hv0 & Htne & Hd1) | (Hvt & Hsd)].
  + apply (HCX fx X ly2 S2 Hp2 W2 (ms_regs ms) (ms_mem ms) _ (k + k1) pos 0 Hn HPRE HEXB3);
      [rewrite R21; exact Ha0|].
    exists (exv_i1 X + Z.of_nat (length wl)), (e_dep X), 1.
    split; [|split; [right; reflexivity|]].
    * split; [replace (e_x0 X + (exv_i1 X + Z.of_nat (length wl))) with (e_x0 X + exv_i1 X + Z.of_nat (length wl)) by lia;
               exact (TP _ _ _ Hq)|].
      split; [exact (TW _ _ _ Cq8 ltac:(lia) ltac:(cbn; lia))|].
      split; [exact (TW _ _ _ Cq16 ltac:(lia) ltac:(cbn; lia))|].
      split; [exact (TW _ _ _ Cq24 ltac:(lia) ltac:(cbn; lia))|].
      exact (TP _ _ _ Hd1).
    * rewrite HV. split; [reflexivity|]. split.
      { rewrite !length_skipn. zl. }
      split; [reflexivity|]. split; [intros _; right; split; [exact Hv0|]|intros _; reflexivity].
      intros Et. apply Htne. apply Htag. exact Et.
  + apply (HCX fx X ly2 S2 Hp2 W2 (ms_regs ms) (ms_mem ms) _ (k + k1) pos 0 Hn HPRE HEXB3);
      [rewrite R21; exact Ha0|].
    exists (exv_i1 X + Z.of_nat (length wl)), (e_dep X), (e_dl X).
    split; [|split; [exact HPdl|]].
    * split; [replace (e_x0 X + (exv_i1 X + Z.of_nat (length wl))) with (e_x0 X + exv_i1 X + Z.of_nat (length wl)) by lia;
               exact (TP _ _ _ Hq)|].
      split; [exact (TW _ _ _ Cq8 ltac:(lia) ltac:(cbn; lia))|].
      split; [exact (TW _ _ _ Cq16 ltac:(lia) ltac:(cbn; lia))|].
      split; [exact (TW _ _ _ Cq24 ltac:(lia) ltac:(cbn; lia))|].
      exact (TS _ _ _ Cq32 Hsd).
    * rewrite HV. split; [reflexivity|]. split.
      { rewrite !length_skipn. zl. }
      split; [reflexivity|]. split; [intros Hd; left; exact Hd|].
      intros [Hd | (Hv0 & Hne)]; [exact Hd|]. exfalso.
      destruct Hvt as [Hv | Ht]; [exact (Hv0 Hv)|]. apply Hne. apply Htag. exact Ht.
- (* no match: r = -1, the cursor unchanged *)
  assert (Hpre : PjGrammar.prefixb wl (skipn (Z.to_nat (exv_i1 X)) (e_x X)) = false).
  { destruct (PjGrammar.prefixb wl (skipn (Z.to_nat (exv_i1 X)) (e_x X))) eqn:Ep; [|reflexivity].
    exfalso. apply Hmiss. apply (proj2 HH). reflexivity. }
  rewrite Hpre in HV.
  apply (HCX fx X ly2 S2 Hp2 W2 (ms_regs ms) (ms_mem ms) _ (k + k1) pos (-1) Hn HPRE HEXB3);
    [rewrite R21; exact Ha0|].
  exists (exv_i1 X), (e_dep X), (e_dl X).
  split; [|split; [exact HPdl|]].
  + split; [exact (TS _ _ _ Cq Hsq)|].
    split; [exact (TW _ _ _ Cq8 ltac:(lia) ltac:(cbn; lia))|].
    split; [exact (TW _ _ _ Cq16 ltac:(lia) ltac:(cbn; lia))|].
    split; [exact (TW _ _ _ Cq24 ltac:(lia) ltac:(cbn; lia))|].
    exact (TS _ _ _ Cq32 Hsd).
  + rewrite HV. split; [reflexivity|]. split; [exact Hi1r|]. lia.
Qed.
End f.

(* ---- the arm lemma (ExvB_Disp_arms.v's EXVD_WORD, from the exit cut) ---- *)
Lemma exvd_word_holds : forall n, (forall fx : YK11.FPState, CUT_CX (fx := fx) B ARx SK n) ->
  forall fx : YK11.FPState, EXVD_WORD (fx := fx) B ARx SK n.
Proof. intros n HCX fx. exact (exw_at (fx := fx) n HCX). Qed.
End s.

Print Assumptions exvd_word_holds.
