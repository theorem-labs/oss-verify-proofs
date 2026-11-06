(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Rebound onto the old-pin kit of record (4f18c75d4900): EXB carries the memnorm keep from the entry
   memory (exv_rm); the runs carry it by YC1fPx.v's _inv runners, exv_kt (ExvB_Open_kt.v) takes it at every exit. *)
(* Theorem Labs, 2026-10: fuzz_preset, image B (asan-ubsan, rebuilt pin f8f98a95bc52, unstripped twin 3b5e1a099b53),
   ex_value, segment C1 DISP (lane ExvDisp): THE DISPATCH RUN, from CUT_C1 (exv_pc 0x11c = B 0x83648, after ex_ws
   returned) to the segment's exits, over B's whole-range listing with the paj engine (YC1fPx.v over YCbqG's
   ajournal_x), as WalkS8a's image-A dispatch lib/A/Prog/S8aDisp.v (cold/h-hpreset-7-walk-S8a) does.
   - B 0x83648-0x83680: the UBSan check `bnez (q & 7)` (q mod 8 = 0: the fact on atom 19), the two ASan checks of q
     and q + 8 (shadow entry of [q, q + 16), zero: q on the real stack), p = in->p, e = in->end, s5 = -1, the test
     p >= e: taken only at the end of the text (exvd_c1_end, to CUT_CX with r = -1: exv_V E = None by exvd_V_end).
   - B 0x83684-0x836a8 (exvd_c1_byte): the UBSan check `beqz p` (4096 <= p), 152(s1) := v, the ASan check of the
     byte at p (shadow entry of the text byte, from src_rd), c = the byte, 144(s1) := shadow (q), then the switch:
     c > 109: 'n' (B 0x83790) and 't' (B 0x83948) to EXVD_WORD at exv_pc 0x42c, '{' to CUT_CI (a0 = 125) at
     exv_pc 0x374, else CUT_CN at exv_pc 0x278; c <= 109: the quote (34) to EXVD_STR at exv_pc 0x1d0, '[' to CUT_CI (a0 = 93),
     'f' (B 0x836c4) to EXVD_WORD, else CUT_CN. Every UBSan trap (B 0x8407c) and ASan report (B 0x84080 partial path
     back to 0x8369c, 0x84190, 0x84198) is resolved not taken inside the runs from the facts and shadow entries.
   - EXB at every exit: ExvOpen's exv_kt (ExvB_Open_kt.v; the run writes only 144(s1) and 152(s1)).
   Numerals: 0x11c, 0x1d0, 0x278, 0x374, 0x42c, 0xa7c (DERIVED: cut / arm pcs minus ex_value's entry, the internal file neutral_dis.py
   on the rebuilt image); 144, 152, 160, 176 (LENGTH: spill slots of B's code and the exv_kt window); 34, 91, 102,
   109, 110, 116, 123, 93, 125 (WORD: ASCII bytes the code compares / loads); 0x10f40, 0x10f60, 0x10f80 (DERIVED:
   PAddHi offsets of the literals from B_prog_val (A_OBJ 2)); 0x7fff7f800000 (DERIVED: the least alloc_ceiling,
   asan_consts); 8, 16, 40, 56, 2 ^ 44, 2 ^ 47, 2 ^ 63, 2 ^ 64, 4096, 255 (LENGTH / DERIVED: widths, alignments,
   address-space bounds); atom indices 2-34, 243 (DERIVED: Ereg / Eimg atoms; 243 = A_OBJ 2). No ADDRESS. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn
YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YCbqG YCbqGcall.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YImgTop YGcfNames YGcfRoomKeep FCiface.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_FnEx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_Reader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import PRH_ImgB Img0 Listing_prog PAImg_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm YSRrMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import ExvB_Stmt ExvB_Open_kt ExvB_Disp_arms.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope bv_scope.
Open Scope Z_scope.

#[local] Existing Instance prh_img_B.
(* plain lia (YZ00's `lia` prunes hypotheses and fails on goals over record projections) *)
Ltac zl := Zify.zify; xlia zchecker.

(* ---- the symbolic states of the dispatch (closed terms: the engine vm_computes from them) ---- *)
Definition EXVD_EV0 : Z := B_prog_sigma AS_ex_value - B_prog_base.
Definition EXVD_QLO : Z := 0x7fff7f800000.
Definition EXVD_Bx : sv := SOff 25 0.
Definition EXVD_Bspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
(* C1 at the end of the text: in at s3 (atom 19), in->p = atom 32, in->end = atom 33 *)
Definition ss_c1e : sstate :=
  mkSS (EXVD_EV0 + 0x11c) sr_atoms
    [ YP09.mkRegion (Some 19%nat) 0 16 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 32 0)); YP09.mkChunk 8 (CVal 8 (SOff 33 0))] ]
    None (mkFacts [ (25%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (19%nat, mkAF EXVD_QLO (2 ^ 47 - 40) 3);
                    (32%nat, mkAF 4096 (2 ^ 47 - 1) 0); (33%nat, mkAF 4096 (2 ^ 47 - 1) 0) ] [] []).
Definition SH_c1e : list shent := [mkSHE 19 0 16].
(* C1 before a byte: also the spill slots [s1 + 144, s1 + 160) (s1 = atom 9) and the byte at in->p (atom 34) *)
Definition ss_c1b : sstate :=
  mkSS (EXVD_EV0 + 0x11c) sr_atoms
    [ YP09.mkRegion (Some 19%nat) 0 16 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 32 0)); YP09.mkChunk 8 (CVal 8 (SOff 33 0))];
      YP09.mkRegion (Some 9%nat) 144 160 144 160 [];
      YP09.mkRegion (Some 32%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 34 0))] ]
    None (mkFacts [ (25%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (19%nat, mkAF EXVD_QLO (2 ^ 47 - 40) 3);
                    (32%nat, mkAF 4096 (2 ^ 47 - 1) 0); (33%nat, mkAF 4096 (2 ^ 47 - 1) 0); (34%nat, mkAF 0 255 0);
                    (9%nat, mkAF EXVD_QLO (2 ^ 47) 5) ] [] []).
Definition SH_c1b : list shent := [mkSHE 19 0 16; mkSHE 32 0 1].

(* ---- journal-free helpers (S8aDisp.v's / ex_ws_x.v's idioms, restated) ---- *)
Lemma exvd_pc_eq : forall off, exv_pc off = B_prog_val A_TEXT + (EXVD_EV0 + off).
Proof.
intros off. assert (H2 : B_prog_val A_TEXT = B_prog_base) by (vm_compute; reflexivity).
rewrite H2. unfold exv_pc, EXVD_EV0. zl.
Qed.
Lemma exvd_denot_atom : forall E n v, ew E n = w64 v -> 0 <= v < 2 ^ 64 -> sv_denot E (SOff n 0) = Z_to_bv 64 v.
Proof.
intros E n v H Hv. apply bv_eq. rewrite denot_SOff, H. unfold w64. rewrite !unsigned_lit_small by lia. rewrite Z.add_0_r.
apply zcanon_id. unfold M64. lia.
Qed.
Lemma exvd_frame_ro : forall E (rs : smem) (m m' : word -> option byte),
  frame_of E rs m m' -> forallb (fun r => YP09.r_whi r <=? YP09.r_wlo r) rs = true -> forall x, m' x = m x.
Proof.
intros E rs m m' HF Hro x. apply HF. intros (r & Hin & Hr). rewrite forallb_forall in Hro.
specialize (Hro r Hin). apply Z.leb_le in Hro. lia.
Qed.
Lemma exvd_frame_slot : forall E rs (m m' : word -> option byte) lo hi, frame_of E rs m m' ->
  (forall z, in_wrange E rs z -> lo <= z < hi) -> forall x, ~ (lo <= bv_unsigned x < hi) -> m' x = m x.
Proof. intros E rs m m' lo hi HF Hw x Hx. apply HF. intros H. exact (Hx (Hw _ H)). Qed.
Lemma exvd_vm_eq : forall (m m' : word -> option byte) a n v, (forall x, m' x = m x) ->
  val_mem rsegs m a n v -> val_mem rsegs m' a n v.
Proof. intros m m' a n v H Hv kk Hk. unfold mbyte. rewrite H. exact (Hv kk Hk). Qed.
Lemma exvd_blt_U : forall E a b, U E a < 2 ^ 63 -> U E b < 2 ^ 63 ->
  branch_taken BC_LT (sv_denot E a) (sv_denot E b) = (U E a <? U E b).
Proof.
intros E a b Ha Hb. pose proof (U_range E a) as Ra. pose proof (U_range E b) as Rb. unfold M64 in *.
cbn [branch_taken]. unfold bv_lts. rewrite !signed_is_swrap_unsigned. fold (U E a). fold (U E b).
unfold bv_swrap, bv_wrap.
replace (bv_half_modulus 64) with (2 ^ 63) by reflexivity. replace (bv_modulus 64) with (2 ^ 64) by reflexivity.
rewrite !Z.mod_small by zl.
replace (U E a + 2 ^ 63 - 2 ^ 63) with (U E a) by zl. replace (U E b + 2 ^ 63 - 2 ^ 63) with (U E b) by zl. reflexivity.
Qed.
Lemma exvd_blt_lit : forall E n v z, ew E n = w64 v -> 0 <= v < 2 ^ 63 -> 0 <= z < 2 ^ 63 ->
  branch_taken BC_LT (sv_denot E (SLit z)) (sv_denot E (SOff n 0)) = (z <? v).
Proof.
intros E n v z H Hv Hz. rewrite exvd_blt_U; rewrite ?U_SLit, ?(U_atom E n v H) by zl; rewrite ?zcanon_id by (unfold M64; zl);
  [reflexivity | zl | zl].
Qed.
Lemma exvd_beq_lit : forall E n v z, ew E n = w64 v -> 0 <= v < 2 ^ 64 -> 0 <= z < 2 ^ 64 ->
  branch_taken BC_EQ (sv_denot E (SOff n 0)) (sv_denot E (SLit z)) = (v =? z).
Proof. intros E n v z H Hv Hz. rewrite branch_eq_U, U_SLit, (U_atom E n v H) by zl. rewrite zcanon_id by (unfold M64; zl). reflexivity. Qed.
Lemma exvd_bne_lit : forall E n v z, ew E n = w64 v -> 0 <= v < 2 ^ 64 -> 0 <= z < 2 ^ 64 ->
  branch_taken BC_NE (sv_denot E (SOff n 0)) (sv_denot E (SLit z)) = negb (v =? z).
Proof. intros E n v z H Hv Hz. rewrite branch_ne_U, U_SLit, (U_atom E n v H) by zl. rewrite zcanon_id by (unfold M64; zl). reflexivity. Qed.
Ltac exvd_uat n v Hn H :=
  match type of H with context [U ?E' (SOff n 0)] =>
    let Hx := fresh "Hx" in assert (Hx : ew E' n = w64 v) by (cbn [ew ewset Nat.eqb]; exact Hn);
    rewrite (U_atom E' n v Hx) in H by zl; clear Hx end.
Ltac exvd_brl c E34 H :=
  first [ rewrite (exvd_blt_lit _ 34%nat c) in H; [ | cbn [ew ewset Nat.eqb]; exact E34 | zl | zl ]
        | rewrite (exvd_beq_lit _ 34%nat c) in H; [ | cbn [ew ewset Nat.eqb]; exact E34 | zl | zl ]
        | rewrite (exvd_bne_lit _ 34%nat c) in H; [ | cbn [ew ewset Nat.eqb]; exact E34 | zl | zl ] ].
(* the shadow address the code computes: (x >> 3) + s9 *)
Lemma exvd_denot_shx : forall E n m v sb c, ew E n = w64 v -> ew E m = w64 sb -> 0 <= v < 2 ^ 63 -> v + c < 2 ^ 63 ->
  0 <= v + c -> 0 <= sb < 2 ^ 32 ->
  sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff n c) (SLit 3)) (SOff m 0)) = Z_to_bv 64 (sb + (v + c) / 8).
Proof.
intros E n m v sb c Hn Hm Hv0 Hv Hvc Hsb. unfold w64 in *.
rewrite <- (Z_to_bv_bv_unsigned 64 (sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff n c) (SLit 3)) (SOff m 0)))). f_equal.
change (U E (SAlu ALU_ADD (SAlu ALU_SRL (SOff n c) (SLit 3)) (SOff m 0)) = sb + (v + c) / 8).
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SOff, Hn, Hm. rewrite !unsigned_lit_small by zl.
rewrite Z.add_0_r.
change (Z.land (U E (SLit 3)) 63) with 3. rewrite Z.shiftr_div_pow2 by zl. change (2 ^ 3) with 8.
pose proof (Z.div_pos (v + c) 8 ltac:(zl) ltac:(zl)). pose proof (Z.div_lt_upper_bound (v + c) 8 (2 ^ 60) ltac:(zl) ltac:(zl)).
rewrite (zcanon_id (v + c)) by (unfold M64; zl). rewrite (zcanon_id ((v + c) / 8)) by (unfold M64; zl).
rewrite (zcanon_id sb) by (unfold M64; zl). rewrite zcanon_id by (unfold M64; zl). zl.
Qed.
Lemma exvd_aview_kept : forall (H : word -> bool) (m m' : word -> option byte) (P : Z -> Prop),
  (forall x : word, ~ P (bv_unsigned x) -> mrestrict H m' x = mrestrict H m x) ->
  forall a, 0 <= a < 2 ^ 64 -> ~ P a -> aview rsegs H m' a = aview rsegs H m a.
Proof.
intros H m m' P HK a Ha Hn. unfold aview, mbyte. rewrite HK; [reflexivity|].
rewrite unsigned_lit_small by zl. exact Hn.
Qed.
Lemma exvd_vm_kept : forall (m m' : word -> option byte) (P : Z -> Prop) a n v,
  (forall x : word, ~ P (bv_unsigned x) -> m' x = m x) -> 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  (forall z, a <= z < a + Z.of_nat n -> ~ P z) -> val_mem rsegs m a n v -> val_mem rsegs m' a n v.
Proof.
intros m m' P a n v HK Ha Hn HP Hv kk Hk. unfold mbyte. rewrite HK; [exact (Hv kk Hk)|].
rewrite unsigned_lit_small by zl. apply HP. zl.
Qed.
Lemma exvd_cfg_eq : forall {fx : YK11.FPState} {rc : YM05.RunCeil} (regs : bvmap 5 word) (mem : word -> option byte) md off n,
  @pa_val _ B_prog_listing PI_prog_B A_TEXT + n = exv_pc off ->
  mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (@pa_val _ B_prog_listing PI_prog_B A_TEXT + n)) mem (YK11.seg_rom rsegs)) md =
  cfg_at rsegs (exv_pc off) regs mem md.
Proof. intros fx rc regs mem md off n H. unfold cfg_at. rewrite <- H. reflexivity. Qed.
Ltac exvd_cfg_to off :=
  lazymatch goal with |- SRr ?sg ?w ?c ?Q =>
    lazymatch c with {| cfg_ms := YK11.mkst ?r _ ?m _; cfg_model := ?d |} =>
      let H := fresh "Hcfg" in
      assert (H : c = cfg_at rsegs (exv_pc off) r m d)
        by (unfold cfg_at; f_equal; f_equal; try reflexivity; unfold w64; f_equal; vm_compute; reflexivity);
      rewrite H; clear H end end.
Lemma exvd_bregs : forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 24; 25; 26]%bv ->
  In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26]%bv.
Proof. intros r H. cbn [In] in *. tauto. Qed.

(* the shadow address of in that the code spills at 144(s1) *)
Definition EXVD_SHQ : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff 19 0) (SLit 3)) (SOff 25 0).
Lemma exvd_field : forall E m n b cs lo hi wlo whi od (w : N) e v,
  region_ok rsegs E m (YP09.mkRegion (Some n) lo hi wlo whi cs) ->
  bv_unsigned (ew E n) = b -> In (YP09.mkChunk od (CVal w e)) cs -> sv_denot E e = Z_to_bv 64 v ->
  0 <= v < 2 ^ (8 * Z.of_N w) -> (Z.of_N w <= 8) ->
  val_mem rsegs m (b + od) (N.to_nat w) v.
Proof.
intros E m n b cs lo hi wlo whi od w e v (_ & _ & _ & Hcs) Hn Hc He Hv Hw.
pose proof (proj1 (Forall_forall _ _) Hcs _ Hc) as Hck. cbn [YP09.r_base base_val] in Hck. rewrite Hn in Hck.
exact (val_of_chunk_ok rsegs E m b od w e v Hck He Hv Hw).
Qed.
Lemma exvd_vm_mod : forall m a v, val_mem rsegs m a 8 (v mod 2 ^ 64) -> val_mem rsegs m a 8 v.
Proof.
intros m a v H kk Hk. rewrite (H kk Hk). do 2 f_equal. unfold YO0f.le_byte.
replace (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) by reflexivity. rewrite Z.mod_mod by lia. reflexivity.
Qed.
Lemma exvd_region1 : forall {fx : YK11.FPState} {rc : YM05.RunCeil} E ss ms (W : world rsegs) r,
  st_ok_pi (@pa_segs _ B_prog_listing PI_prog_B) (@pa_val _ B_prog_listing PI_prog_B) E ss (restrict (w_H W) ms) ->
  nth_error (ss_mem ss) 1 = Some r -> region_ok rsegs E (mrestrict (w_H W) (ms_mem ms)) r.
Proof.
intros fx rc E ss ms W r HS Hr. pose proof (st_ok_mem_ok _ _ _ _ HS) as (_ & HRO & _).
cbn [ss_mem abs_ss setpc ms_mem restrict] in HRO.
exact (proj1 (Forall_forall _ _) HRO r (nth_error_In _ _ Hr)).
Qed.

Section r. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world rsegs -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
Hypothesis HYP : EXV_HYP B ARx SK.
#[local] Notation AJ := (ajournal_x (SK := SK) rsegs B prh_pst ARx).

Lemma exvd_stk : forall E, 16384 <= exv_STK E.
Proof.
intros E. unfold exv_STK, STK_ex_value. replace (zmaxl _) with 16384 by (vm_compute; reflexivity).
assert (HF : 0 <= @pi_frame prh_img_B F_ex_value) by (vm_compute; congruence). nia.
Qed.

(* EXB and the cursor after a stretch of the dispatch that writes only the spill slots [s1 + 144, s1 + 160) *)
Lemma exvd_leaf : forall E lyc Sc Hpc (Wc : world rsegs) (regs : bvmap 5 word) memc mdc k pos regs' memc' mdc' k' p e dep scr dl,
  EXV_PRE B ARx E -> EXB B ARx SK E lyc Sc Hpc Wc regs memc mdc k pos ->
  prhex_cur Wc memc (e_q E) p e dep scr dl ->
  AJ (exv_STK E + e_d E) (exv_sp E + e_d E) (exv_FP E) (e_ly E) (e_S E) (e_Hp E) (e_W E) (e_mem E) (e_md E)
    [(1, pos)] lyc Sc Hpc Wc memc' mdc' k' ->
  (forall x : word, ~ (exv_s1 E + 144 <= bv_unsigned x < exv_s1 E + 160) ->
     mrestrict (w_H Wc) memc' x = mrestrict (w_H Wc) memc x) ->
  (forall a, apresent (w_H Wc) memc a -> apresent (w_H Wc) memc' a) ->
  (YAkMemnorm.memnorm rsegs (e_mem E) -> YAkMemnorm.memnorm rsegs memc') ->
  (forall r, In r [2; 3; 4; 8; 9; 18; 19; 24; 25; 26]%bv -> getr regs' r = getr regs r) ->
  EXB B ARx SK E lyc Sc Hpc Wc regs' memc' mdc' k' pos /\ prhex_cur Wc memc' (e_q E) p e dep scr dl.
Proof.
intros E lyc Sc Hpc Wc regs memc mdc k pos regs' memc' mdc' k' p e dep scr dl HP HB Hcur HJ' HK HG HPM HR.
pose proof (exvd_stk E) as HSTK. pose proof (exv_s1_le E) as ((S1a & S1b) & _).
pose proof HP as HP0. unfold EXV_PRE in HP0. cbv zeta in HP0.
destruct HP0 as (_ & _ & _ & _ & _ & _ & _ & _ & Hspq & Hqd & Hwin & _).
destruct Hwin as (Hd0 & _ & _ & _).
assert (Hsp0 : 0 <= exv_sp E) by (pose proof (bv_unsigned_in_range _ (getr (e_regs E) 2%bv)) as R; unfold exv_sp, spZ in *; zl).
assert (Hq64 : e_q E + 40 <= 2 ^ 64).
{ pose proof (bv_unsigned_in_range _ (getr (e_regs E) 2%bv)) as R. unfold exv_sp, spZ in *. unfold bv_modulus in R.
  pose proof HP as HP1. unfold EXV_PRE in HP1. cbv zeta in HP1.
  destruct HP1 as (HFP & _). destruct HFP as ((_ & _ & _ & _ & _ & Hastk & _) & _).
  destruct Hastk as (_ & _ & _ & _ & _ & H47 & _ & _ & Htop).
  destruct HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & Hdtop & _) & _). unfold spZ in *. zl. }
split.
- apply (exv_kt B ARx SK HYP E lyc Sc Hpc Wc regs memc mdc k pos regs' memc' mdc' k' HP HB HJ').
  + intros a Ha Hn _. apply (exvd_aview_kept _ _ _ (fun z => exv_s1 E + 144 <= z < exv_s1 E + 160) HK a Ha). cbv beta. zl.
  + exact HG.
  + exact HPM.
  + exact HR.
- destruct Hcur as (Q1 & Q2 & Q3 & Q4 & Q5). unfold exv_sp in *.
  repeat split; (eapply (exvd_vm_kept _ _ (fun z => exv_s1 E + 144 <= z < exv_s1 E + 160)); [exact HK | zl | cbn; zl | intros z Hz; cbn in Hz |- *; zl | eassumption]).
Qed.

(* a leaf of the dispatch: EXB, the cursor and the two spills, from the run's final symbolic state *)
Lemma exvd_lfin : forall E lyc Sc Hpc (Wc : world rsegs) (regs : bvmap 5 word) memc mdc k pos Ev ss ms md' k',
  EXV_PRE B ARx E -> EXB B ARx SK E lyc Sc Hpc Wc regs memc mdc k pos ->
  prhex_cur Wc memc (e_q E) (e_x0 E + exv_i1 E) (e_x0 E + exv_len E) (e_dep E) (e_scr E) (e_dl E) ->
  getr regs 27 = w64 (e_v E) ->
  st_ok_pi (@pa_segs _ B_prog_listing PI_prog_B) (@pa_val _ B_prog_listing PI_prog_B) Ev ss (restrict (w_H Wc) ms) ->
  nth_error (ss_mem ss) 1 = Some (YP09.mkRegion (Some 9%nat) 144 160 144 160
    [YP09.mkChunk 144 (CVal 8 EXVD_SHQ); YP09.mkChunk 152 (CVal 8 (SOff 27 0))]) ->
  ew Ev 9 = w64 (exv_s1 E) -> ew Ev 19 = w64 (e_q E) -> ew Ev 25 = w64 SHADOW_OFF -> ew Ev 27 = w64 (e_v E) ->
  AJ (exv_STK E + e_d E) (exv_sp E + e_d E) (exv_FP E) (e_ly E) (e_S E) (e_Hp E) (e_W E) (e_mem E) (e_md E)
    [(1, pos)] lyc Sc Hpc Wc (ms_mem ms) md' k' ->
  (forall x : word, ~ (exv_s1 E + 144 <= bv_unsigned x < exv_s1 E + 160) ->
     mrestrict (w_H Wc) (ms_mem ms) x = mrestrict (w_H Wc) memc x) ->
  (forall a, apresent (w_H Wc) memc a -> apresent (w_H Wc) (ms_mem ms) a) ->
  (YAkMemnorm.memnorm rsegs (e_mem E) -> YAkMemnorm.memnorm rsegs (ms_mem ms)) ->
  (forall r, In r [2; 3; 4; 8; 9; 18; 19; 24; 25; 26]%bv -> getr (ms_regs ms) r = getr regs r) ->
  EXB B ARx SK E lyc Sc Hpc Wc (ms_regs ms) (ms_mem ms) md' k' pos /\
  prhex_cur Wc (ms_mem ms) (e_q E) (e_x0 E + exv_i1 E) (e_x0 E + exv_len E) (e_dep E) (e_scr E) (e_dl E) /\
  exv_spill E Wc (ms_mem ms) 144 (shadow_addr (e_q E)) /\ exv_spill E Wc (ms_mem ms) 152 (e_v E).
Proof.
intros E lyc Sc Hpc Wc regs memc mdc k pos Ev ss ms md' k' HP HB Hcur H27 HS Hr E9 E19 E25 E27 HJ' HK HG HPM HR.
destruct (exvd_leaf E lyc Sc Hpc Wc regs memc mdc k pos (ms_regs ms) (ms_mem ms) md' k' _ _ _ _ _ HP HB Hcur HJ' HK HG HPM HR)
  as [HB' Hcur'].
split; [exact HB'|]. split; [exact Hcur'|].
pose proof (exv_s1_le E) as ((S1a & S1b) & _).
pose proof HP as HP0. unfold EXV_PRE in HP0. cbv zeta in HP0.
destruct HP0 as (HFP & _ & _ & _ & _ & _ & _ & _ & Hspq & Hqd & Hwin & _).
destruct HFP as ((_ & _ & _ & _ & _ & Hastk & _) & _).
destruct Hastk as (_ & Hstk0 & Hceil & Hslo & Hshi & H47 & _ & _ & Htop).
destruct Hwin as (Hd0 & _ & Hdtop & _).
pose proof asan_consts as (C1 & _).
assert (Hsp0 : 0 <= spZ (e_regs E)) by (pose proof (bv_unsigned_in_range _ (getr (e_regs E) 2%bv)) as R; unfold spZ; zl).
unfold exv_sp in S1a, S1b.
pose proof (exvd_stk E) as HSTK. unfold exv_STK in HSTK.
pose proof (exvd_region1 Ev ss ms Wc _ HS Hr) as RG.
unfold exv_spill. split.
- assert (V := exvd_field Ev _ 9 (exv_s1 E) _ 144 160 144 160 144 8 EXVD_SHQ (shadow_addr (e_q E)) RG
    ltac:(rewrite E9; unfold w64; apply unsigned_lit_small; zl) ltac:(left; reflexivity)
    ltac:(unfold EXVD_SHQ; rewrite (exvd_denot_shx Ev 19 25 (e_q E) SHADOW_OFF 0 E19 E25) by (unfold SHADOW_OFF; zl);
          unfold shadow_addr; f_equal; zl)
    ltac:(unfold shadow_addr, SHADOW_OFF; cbn; pose proof (Z.div_pos (e_q E) 8 ltac:(zl) ltac:(zl)); zl) ltac:(cbn; zl)).
  exact V.
- apply exvd_vm_mod.
  assert (V := exvd_field Ev _ 9 (exv_s1 E) _ 144 160 144 160 152 8 (SOff 27 0) (e_v E mod 2 ^ 64) RG
    ltac:(rewrite E9; unfold w64; apply unsigned_lit_small; zl) ltac:(right; left; reflexivity)
    ltac:(rewrite (exvd_denot_atom Ev 27 (e_v E mod 2 ^ 64)); [reflexivity | | apply Z.mod_pos_bound; zl];
          rewrite E27; unfold w64; apply bv_eq; rewrite !Z_to_bv_unsigned; unfold bv_wrap;
          change (bv_modulus 64) with (2 ^ 64); rewrite Z.mod_mod by lia; reflexivity)
    ltac:(cbn; apply Z.mod_pos_bound; zl) ltac:(cbn; zl)).
  exact V.
Qed.

(* ---- C1 at the end of the text (B 0x83648-0x83680, taken): p >= e, to CUT_CX with r = -1 ---- *)
Lemma exvd_c1_end : forall n E lyc Sc Hpc (Wc : world rsegs) (regs : bvmap 5 word) memc mdc k pos,
  (forall fy : YK11.FPState, CUT_CX (fx := fy) B ARx SK n) ->
  e_n E = n -> EXV_PRE B ARx E -> EXB B ARx SK E lyc Sc Hpc Wc regs memc mdc k pos ->
  prhex_cur Wc memc (e_q E) (e_x0 E + exv_i1 E) (e_x0 E + exv_len E) (e_dep E) (e_scr E) (e_dl E) ->
  exv_len E <= exv_i1 E ->
  SRr rsegs Wc (cfg_at rsegs (exv_pc 0x11c) regs memc mdc) (EXV_POST B ARx SK E).
Proof.
intros n E lyc Sc Hpc Wc regs memc mdc k pos CX Hn HP HB Hcur Hend.
pose proof (eh_laws B ARx SK HYP) as LAWS.
pose proof asan_consts as (C1 & _).
pose proof (exvd_i1_range E) as Hi1.
pose proof HP as HP0. unfold EXV_PRE in HP0. cbv zeta in HP0.
destruct HP0 as (HFP & _ & _ & _ & _ & _ & Hq8 & _ & Hspq & Hqd & Hwin & Hsrc0 & _ & Hlen & Hi0 & Hdep & _ & Hdl & _).
destruct HFP as ((_ & _ & _ & _ & _ & Hastk & _) & _ & Hstk64 & _).
destruct Hastk as (Hal & Hstk0 & Hceil & Hslo & Hshi & H47 & _ & Htop1 & Htop).
destruct Hwin as (Hd0 & Hd16 & Hdtop & _).
destruct Hsrc0 as (_ & Hx4096 & Hxc & _).
pose proof HB as HB0. unfold EXB in HB0. cbv zeta in HB0.
destruct HB0 as (HJ & _ & _ & _ & _ & _ & HRM & _ & _ & R2 & R8 & R9 & R18 & R24 & R25 & R26 & R19 & _ & _ & _ & _ & _ & _
  & _ & _ & _ & HQR & _).
pose proof Hcur as (Q1 & Q2 & Q3 & Q4 & Q5).
unfold exv_len, exv_STK in *.
assert (Hsp0 : 0 <= spZ (e_regs E)) by (pose proof (bv_unsigned_in_range _ (getr (e_regs E) 2%bv)) as R; unfold spZ; zl).
remember (Eimg (Ereg regs [w64 (e_x0 E + exv_i1 E); w64 (e_x0 E + Z.of_nat (length (e_x E)))])) as Ev eqn:HEv.
assert (HEI : img_env (@pa_val _ B_prog_listing PI_prog_B) A_LIM Ev) by (subst Ev; apply Eimg_env).
assert (EL : forall m, (m < A_TEXT)%nat ->
  ew Ev m = ew (Ereg regs [w64 (e_x0 E + exv_i1 E); w64 (e_x0 E + Z.of_nat (length (e_x E)))]) m)
  by (intros m Hm; subst Ev; apply Eimg_low; exact Hm).
assert (E19 : ew Ev 19 = w64 (e_q E)) by (rewrite EL by (unfold A_TEXT; zl); rewrite (ew_Ereg_nat regs _ 19 19%bv eq_refl); exact R19).
assert (E25 : ew Ev 25 = w64 SHADOW_OFF) by (rewrite EL by (unfold A_TEXT; zl); rewrite (ew_Ereg_nat regs _ 25 25%bv eq_refl); exact R25).
assert (E32 : ew Ev 32 = w64 (e_x0 E + exv_i1 E)) by (rewrite EL by (unfold A_TEXT; zl); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew Ev 33 = w64 (e_x0 E + Z.of_nat (length (e_x E)))) by (rewrite EL by (unfold A_TEXT; zl); exact (ew_Ereg_extra regs _ 1)).
assert (HAE : env_agree 32 (Ereg regs [w64 (e_x0 E + exv_i1 E); w64 (e_x0 E + Z.of_nat (length (e_x E)))]) Ev)
  by (subst Ev; split; [intros m Hm; apply Eimg_low; unfold A_TEXT; zl | reflexivity]).
clear EL.
assert (HS : st_ok_pi (@pa_segs _ B_prog_listing PI_prog_B) (@pa_val _ B_prog_listing PI_prog_B) Ev ss_c1e
  (restrict (w_H Wc) (@YK11.mkst fx regs (Z_to_bv 64 (@pa_val _ B_prog_listing PI_prog_B A_TEXT + (EXVD_EV0 + 0x11c)))
     memc (YK11.seg_rom (@pa_segs _ B_prog_listing PI_prog_B))))).
{ rewrite restrict_mkst_fx. unfold ss_c1e. apply pa_entry_st_ok_full.
  - subst Ev. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor]. unfold region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E19. unfold w64. rewrite unsigned_lit_small by zl.
    split; [zl|]. split; [zl|]. split; [intros o Ho; zl|].
    constructor; [|constructor; [|constructor]].
    + apply (chunk_ok_val rsegs Ev _ (e_q E) 0 8 (SOff 32 0) (e_x0 E + exv_i1 E));
        [exact (exvd_denot_atom Ev 32 _ E32 ltac:(zl)) | zl | zl |].
      rewrite Z.add_0_r. exact Q1.
    + apply (chunk_ok_val rsegs Ev _ (e_q E) 8 8 (SOff 33 0) (e_x0 E + Z.of_nat (length (e_x E))));
        [exact (exvd_denot_atom Ev 33 _ E33 ltac:(zl)) | zl | zl | exact Q2].
  - cbn [pairwise_disjoint all_disjoint]. split; exact I.
  - split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E25, E19, E32, E33. unfold w64. rewrite !unsigned_lit_small by (unfold SHADOW_OFF; zl).
    change (2 ^ 0) with 1. change (2 ^ 3) with 8. rewrite !Z.mod_1_r. unfold EXVD_QLO, SHADOW_OFF. repeat split; zl. }
assert (SHOK : sh_ok rsegs EXVD_Bx SH_c1e Ev (mrestrict (w_H Wc) memc)).
{ constructor; [|constructor].
  apply (shent_ok_of_range rsegs (w_H Wc) memc Ev EXVD_Bx 19 (e_q E) 40 (e_q E) 0 16 HQR);
    [ unfold EXVD_Bx; apply (U_atom Ev 25 SHADOW_OFF E25); unfold SHADOW_OFF; zl
    | apply (U_atom Ev 19 (e_q E) E19); zl | zl | zl |].
  intros z Hz. unfold SHADOW_OFF. zl. }
unfold cfg_at. rewrite (exvd_pc_eq 0x11c). unfold w64.
change (B_prog_val A_TEXT) with (@pa_val _ B_prog_listing PI_prog_B A_TEXT).
(* memnorm carried as P m := memnorm (e_mem E) -> memnorm m (YSRrMemnorm.v), by the _inv runners *)
pose proof (proj2 HRM) as HPM.
pose proof (YSRrMemnorm.srr_inv_laws_imp rsegs _ (e_mem E) (YSRrMemnorm.srr_inv_laws_memnorm_k rsegs)) as PLAW.
pose (RUN := paj_run_x_inv (fx := fx) (rc := rc) (SK := SK) (L := B_prog_listing) (PL := PL_prog_B) (PI := PI_prog_B)
  B prh_pst ARx LAWS _ PLAW).
pose (RUNTO := paj_run_to_x_inv (fx := fx) (rc := rc) (SK := SK) (L := B_prog_listing) (PL := PL_prog_B) (PI := PI_prog_B)
  B prh_pst ARx LAWS _ PLAW).
pose (BR := paj_branch (fx := fx) (PI := PI_prog_B)).
paj_run_tok_x_inv RUN HS HJ SHOK HPM EXVD_Bspan.
{ lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp ?fp ?b0 ?bc ?ly' ?own => let rs' := eval vm_compute in rs in
    change (awr_ok Ex rs' stk sp fp b0 bc ly' own) end.
  repeat (apply awr_ok_cons_ro; [cbn; zl|]). apply awr_ok_nil. }
pose proof (exvd_frame_ro _ _ _ _ HFr ltac:(vm_compute; reflexivity)) as HM1. clear HF HFr. rename HG into HG1.
psrr_branch_tok RUN BR HS SHOK EXVD_Bspan.
- (* p >= e: the end of the text *)
  paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM EXVD_Bspan (EXVD_EV0 + 0xa7c).
  { lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp ?fp ?b0 ?bc ?ly' ?own => let rs' := eval vm_compute in rs in
      change (awr_ok Ex rs' stk sp fp b0 bc ly' own) end.
    repeat (apply awr_ok_cons_ro; [cbn; zl|]). apply awr_ok_nil. }
  pose proof (exvd_frame_ro _ _ _ _ HFr ltac:(vm_compute; reflexivity)) as HM2. clear HF HFr. rename HG into HG2.
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ [2; 3; 4; 8; 9; 18; 19; 24; 25; 26]%bv HS
    ltac:(first [exact HAE | env_agree_chain HAE]) ltac:(vm_compute; reflexivity)) as HK.
  cbn [ms_regs restrict] in HK.
  prreg HS (21%bv : bv 5) N21.
  pmkst HS. exvd_cfg_to 0xa7c.
  lazymatch goal with |- SRr _ _ (cfg_at _ _ ?rg ?mm ?dd) _ =>
    destruct (exvd_leaf E lyc Sc Hpc Wc regs memc mdc k pos rg mm dd _ _ _ _ _ _ HP HB Hcur HJ) as [HB' Hcur'] end.
  + intros x _. rewrite HM2. exact (HM1 x).
  + intros a Ha. apply (apresent_grows _ _ _ a HG2). apply (apresent_grows _ _ _ a HG1). exact Ha.
  + exact HPM.
  + exact HK.
  + apply (CX fx E lyc Sc Hpc Wc _ _ _ _ pos (-1) Hn HP HB').
    * rewrite N21. apply bv_eq. reflexivity.
    * unfold EXV_RES. exists (exv_len E), (e_dep E), (e_dl E).
      assert (Ei : exv_i1 E = exv_len E) by (unfold exv_len; zl).
      rewrite Ei in Hcur'. unfold exv_len in *.
      split; [exact Hcur'|]. split; [exact Hdl|].
      rewrite (exvd_V_end E ltac:(unfold exv_len; zl) ltac:(unfold exv_len; zl)).
      split; [reflexivity|]. split; zl.
- (* p < e: refuted at the end of the text *)
  exfalso. rewrite branch_geu_U in Hc. exvd_uat 32%nat (e_x0 E + exv_i1 E) E32 Hc.
  exvd_uat 33%nat (e_x0 E + Z.of_nat (length (e_x E))) E33 Hc.
  apply negb_false_iff, Z.ltb_lt in Hc. zl.
Qed.

(* ---- the byte segment's run steps (state: in ro, the spill slots [s1 + 144, s1 + 160) writable, the byte ro) ---- *)
Ltac exvd_awr_b s1 E9 :=
  lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp ?fp ?b0 ?bc ?ly' ?own => let rs' := eval vm_compute in rs in
    change (awr_ok Ex rs' stk sp fp b0 bc ly' own) end;
  apply awr_ok_cons_ro; [cbn; zl|];
  (eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 9%nat s1);
    [ reflexivity
    | cbn [ew ewset Nat.eqb]; rewrite E9; unfold w64; rewrite unsigned_lit_small by zl; reflexivity
    | intros z Hz; cbn [YP09.r_wlo YP09.r_whi] in Hz; left; zl
    | apply awr_ok_cons_ro; [cbn; zl|]; apply awr_ok_nil ]).
Ltac exvd_slot E9 :=
  let z := fresh "z" in let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
  intros z (r & Hin & Hr); vm_compute in Hin;
  repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
    try (cbn [ew ewset Nat.eqb] in Hr; rewrite E9 in Hr; unfold w64 in Hr; rewrite unsigned_lit_small in Hr by zl); zl|]);
  destruct Hin.
Ltac exvd_step s1 E9 HMacc HGacc :=
  let Hst := fresh "Hst" in
  lazymatch goal with HFr : frame_of _ _ (mrestrict _ _) (mrestrict _ _) |- _ =>
    pose proof (exvd_frame_slot _ _ _ _ (s1 + 144) (s1 + 160) HFr ltac:(exvd_slot E9)) as Hst end;
  let H2 := fresh "Hacc" in
  pose proof (fun x Hx => eq_trans (Hst x Hx) (HMacc x Hx)) as H2; clear Hst HMacc; rename H2 into HMacc;
  lazymatch goal with HG : mem_grows _ _ |- _ =>
    let H3 := fresh "Gacc" in
    pose proof (fun a Ha => apresent_grows _ _ _ a HG (HGacc a Ha)) as H3; clear HGacc HG; rename H3 into HGacc end;
  repeat match goal with Hx : frame_of _ _ _ _ |- _ => clear Hx end.
Ltac exvd_ew E1 := cbn [ew ewset Nat.eqb]; first [exact E1 | rewrite !ew_ewset_other by lia; exact E1].
Ltac exvd_shq HS r n c E19 E25 Hr :=
  pose proof (st_ok_pi_restrict_reg _ _ _ _ r HS) as Hr;
  lazymatch type of Hr with _ = sv_denot ?Ex (sr_get ?l _) =>
    let e := eval vm_compute in (sr_get l r) in change (sr_get l r) with e in Hr;
    rewrite (exvd_denot_shx Ex n 25 _ SHADOW_OFF c ltac:(exvd_ew E19) ltac:(exvd_ew E25)) in Hr by (unfold SHADOW_OFF; zl) end;
  cbn [ms_regs restrict] in Hr.

(* ---- C1 before a byte (B 0x83648-0x836a8 and the switch): p < e ---- *)
Lemma exvd_c1_byte : forall n E lyc Sc Hpc (Wc : world rsegs) (regs : bvmap 5 word) memc mdc k pos,
  (forall fy : YK11.FPState, CUT_CN (fx := fy) B ARx SK n) -> (forall fy : YK11.FPState, CUT_CI (fx := fy) B ARx SK n) ->
  (forall fy : YK11.FPState, EXVD_STR (fx := fy) B ARx SK n) -> (forall fy : YK11.FPState, EXVD_WORD (fx := fy) B ARx SK n) ->
  e_n E = n -> EXV_PRE B ARx E -> EXB B ARx SK E lyc Sc Hpc Wc regs memc mdc k pos ->
  prhex_cur Wc memc (e_q E) (e_x0 E + exv_i1 E) (e_x0 E + exv_len E) (e_dep E) (e_scr E) (e_dl E) ->
  getr regs 27 = w64 (e_v E) -> exv_i1 E < exv_len E ->
  SRr rsegs Wc (cfg_at rsegs (exv_pc 0x11c) regs memc mdc) (EXV_POST B ARx SK E).
Proof.
intros n E lyc Sc Hpc Wc regs memc mdc k pos CN CI STR WORD Hn HP HB Hcur H27 Hi1l.
pose proof (eh_laws B ARx SK HYP) as LAWS.
pose proof asan_consts as (C1 & _).
pose proof (exvd_i1_range E) as Hi1.
pose proof (exvd_stk E) as HSTK.
pose proof (exv_s1_le E) as ((S1a & S1b) & S1m).
pose proof HP as HP0. unfold EXV_PRE in HP0. cbv zeta in HP0.
destruct HP0 as (HFP & _ & _ & _ & _ & _ & Hq8 & _ & Hspq & Hqd & Hwin & Hsrc0 & _ & Hlen & Hi0 & Hdep & _ & Hdl & _).
destruct HFP as ((_ & _ & _ & _ & _ & Hastk & _) & _ & Hstk64 & _).
destruct Hastk as (Hal & Hstk0 & Hceil & Hslo & Hshi & H47 & _ & Htop1 & Htop).
destruct Hwin as (Hd0 & Hd16 & Hdtop & _).
destruct Hsrc0 as (_ & Hx4096 & Hxc & _).
pose proof HB as HB0. unfold EXB in HB0. cbv zeta in HB0.
destruct HB0 as (HJ & _ & _ & _ & _ & _ & HRM & _ & _ & R2 & R8 & R9 & R18 & R24 & R25 & R26 & R19 & _ & _ & _ & _ & _ & HSRC
  & HTB & _ & _ & HQR & _).
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
pose proof Hcur as (Q1 & Q2 & Q3 & Q4 & Q5).
destruct HSRC as (Hby & _ & _ & _ & Hra & _).
unfold exv_len, exv_STK, exv_sp in *.
assert (Hsp0 : 0 <= spZ (e_regs E)) by (pose proof (bv_unsigned_in_range _ (getr (e_regs E) 2%bv)) as R; unfold spZ; zl).
assert (Hj : (Z.to_nat (exv_i1 E) < length (e_x E))%nat) by zl.
set (c := nth (Z.to_nat (exv_i1 E)) (e_x E) 0).
destruct (Hby _ Hj) as [Vc Rc]. fold c in Vc, Rc.
rewrite Z2Nat.id in Vc by zl.
(* the text byte lies in an allocator block: an application address apart from the shadow *)
assert (Happ : in_app (e_x0 E + exv_i1 E) 1).
{ destruct (HTB ltac:(zl)) as (b & m & Hbm & Hb & Hbe & _).
  destruct (alx_blocks rsegs B ARx LAWS _ _ _ _ _ _ _ _ HAR Hbm) as (_ & _ & _ & Happ & _).
  assert (Rm : m <= req_size m) by (unfold req_size; destruct (Z.eqb_spec m 0); zl).
  apply (in_app_sub b (req_size m)); [exact Happ | zl | zl | zl]. }
remember (Eimg (Ereg regs [w64 (e_x0 E + exv_i1 E); w64 (e_x0 E + Z.of_nat (length (e_x E))); w64 c])) as Ev eqn:HEv.
assert (HEI : img_env (@pa_val _ B_prog_listing PI_prog_B) A_LIM Ev) by (subst Ev; apply Eimg_env).
assert (EL : forall m, (m < A_TEXT)%nat ->
  ew Ev m = ew (Ereg regs [w64 (e_x0 E + exv_i1 E); w64 (e_x0 E + Z.of_nat (length (e_x E))); w64 c]) m)
  by (intros m Hm; subst Ev; apply Eimg_low; exact Hm).
assert (E9 : ew Ev 9 = w64 (exv_s1 E)) by (rewrite EL by (unfold A_TEXT; zl); rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact R9).
assert (E19 : ew Ev 19 = w64 (e_q E)) by (rewrite EL by (unfold A_TEXT; zl); rewrite (ew_Ereg_nat regs _ 19 19%bv eq_refl); exact R19).
assert (E25 : ew Ev 25 = w64 SHADOW_OFF) by (rewrite EL by (unfold A_TEXT; zl); rewrite (ew_Ereg_nat regs _ 25 25%bv eq_refl); exact R25).
assert (E27 : ew Ev 27 = w64 (e_v E)) by (rewrite EL by (unfold A_TEXT; zl); rewrite (ew_Ereg_nat regs _ 27 27%bv eq_refl); exact H27).
assert (E32 : ew Ev 32 = w64 (e_x0 E + exv_i1 E)) by (rewrite EL by (unfold A_TEXT; zl); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew Ev 33 = w64 (e_x0 E + Z.of_nat (length (e_x E)))) by (rewrite EL by (unfold A_TEXT; zl); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew Ev 34 = w64 c) by (rewrite EL by (unfold A_TEXT; zl); exact (ew_Ereg_extra regs _ 2)).
assert (HAE : env_agree 32 (Ereg regs [w64 (e_x0 E + exv_i1 E); w64 (e_x0 E + Z.of_nat (length (e_x E))); w64 c]) Ev)
  by (subst Ev; split; [intros m Hm; apply Eimg_low; unfold A_TEXT; zl | reflexivity]).
clear EL.
assert (HS : st_ok_pi (@pa_segs _ B_prog_listing PI_prog_B) (@pa_val _ B_prog_listing PI_prog_B) Ev ss_c1b
  (restrict (w_H Wc) (@YK11.mkst fx regs (Z_to_bv 64 (@pa_val _ B_prog_listing PI_prog_B A_TEXT + (EXVD_EV0 + 0x11c)))
     memc (YK11.seg_rom (@pa_segs _ B_prog_listing PI_prog_B))))).
{ rewrite restrict_mkst_fx. unfold ss_c1b. apply pa_entry_st_ok_full.
  - subst Ev. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor; [|constructor; [|constructor]]]; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    + rewrite E19. unfold w64. rewrite unsigned_lit_small by zl.
      split; [zl|]. split; [zl|]. split; [intros o Ho; zl|].
      constructor; [|constructor; [|constructor]].
      * apply (chunk_ok_val rsegs Ev _ (e_q E) 0 8 (SOff 32 0) (e_x0 E + exv_i1 E));
          [exact (exvd_denot_atom Ev 32 _ E32 ltac:(zl)) | zl | zl |].
        rewrite Z.add_0_r. exact Q1.
      * apply (chunk_ok_val rsegs Ev _ (e_q E) 8 8 (SOff 33 0) (e_x0 E + Z.of_nat (length (e_x E))));
          [exact (exvd_denot_atom Ev 33 _ E33 ltac:(zl)) | zl | zl | exact Q2].
    + rewrite E9. unfold w64. rewrite unsigned_lit_small by zl.
      split; [zl|]. split; [zl|]. split; [|constructor].
      intros o Ho. apply (apresent_writable rsegs). apply Hpres. zl.
    + rewrite E32. unfold w64. rewrite unsigned_lit_small by zl.
      split; [zl|]. split; [zl|]. split; [intros o Ho; zl|].
      constructor; [|constructor].
      apply (chunk_ok_val rsegs Ev _ (e_x0 E + exv_i1 E) 0 1 (SOff 34 0) c);
        [exact (exvd_denot_atom Ev 34 _ E34 ltac:(zl)) | cbn; zl | zl |].
      rewrite Z.add_0_r. exact Vc.
  - cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E19, E9, E32. unfold w64. rewrite !unsigned_lit_small by zl.
    repeat split; zl.
  - split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E25, E19, E32, E33, E34, E9. unfold w64. rewrite !unsigned_lit_small by (unfold SHADOW_OFF; zl).
    change (2 ^ 0) with 1. change (2 ^ 3) with 8. change (2 ^ 5) with 32. rewrite !Z.mod_1_r.
    unfold EXVD_QLO, SHADOW_OFF. repeat split; zl. }
assert (SHOK : sh_ok rsegs EXVD_Bx SH_c1b Ev (mrestrict (w_H Wc) memc)).
{ constructor; [|constructor; [|constructor]].
  - apply (shent_ok_of_range rsegs (w_H Wc) memc Ev EXVD_Bx 19 (e_q E) 40 (e_q E) 0 16 HQR);
      [ unfold EXVD_Bx; apply (U_atom Ev 25 SHADOW_OFF E25); unfold SHADOW_OFF; zl
      | apply (U_atom Ev 19 (e_q E) E19); zl | zl | zl |].
    intros z Hz. unfold SHADOW_OFF. zl.
  - apply (shent_ok_of_range rsegs (w_H Wc) memc Ev EXVD_Bx 32 (e_x0 E) (Z.of_nat (length (e_x E)))
      (e_x0 E + exv_i1 E) 0 1 Hra);
      [ unfold EXVD_Bx; apply (U_atom Ev 25 SHADOW_OFF E25); unfold SHADOW_OFF; zl
      | apply (U_atom Ev 32 _ E32); zl | zl | zl |].
    intros z Hz. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF in Happ |- *. zl. }
unfold cfg_at. rewrite (exvd_pc_eq 0x11c). unfold w64.
change (B_prog_val A_TEXT) with (@pa_val _ B_prog_listing PI_prog_B A_TEXT).
(* memnorm carried as P m := memnorm (e_mem E) -> memnorm m (YSRrMemnorm.v), by the _inv runners *)
pose proof (proj2 HRM) as HPM.
pose proof (YSRrMemnorm.srr_inv_laws_imp rsegs _ (e_mem E) (YSRrMemnorm.srr_inv_laws_memnorm_k rsegs)) as PLAW.
pose (RUN := paj_run_x_inv (fx := fx) (rc := rc) (SK := SK) (L := B_prog_listing) (PL := PL_prog_B) (PI := PI_prog_B)
  B prh_pst ARx LAWS _ PLAW).
pose (RUNTO := paj_run_to_x_inv (fx := fx) (rc := rc) (SK := SK) (L := B_prog_listing) (PL := PL_prog_B) (PI := PI_prog_B)
  B prh_pst ARx LAWS _ PLAW).
pose (BR := paj_branch (fx := fx) (PI := PI_prog_B)).
paj_run_tok_x_inv RUN HS HJ SHOK HPM EXVD_Bspan; [exvd_awr_b (exv_s1 E) E9|].
pose proof (exvd_frame_slot _ _ _ _ (exv_s1 E + 144) (exv_s1 E + 160) HFr ltac:(exvd_slot E9)) as HMacc.
pose proof (fun a Ha => apresent_grows _ _ _ a HG Ha) as HGacc. clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK EXVD_Bspan.
{ (* p >= e: impossible before a byte *)
  exfalso. rewrite branch_geu_U in Hc. exvd_uat 32%nat (e_x0 E + exv_i1 E) E32 Hc.
  exvd_uat 33%nat (e_x0 E + Z.of_nat (length (e_x E))) E33 Hc.
  apply negb_true_iff, Z.ltb_ge in Hc. zl. }
clear Hc.
paj_run_tok_x_inv RUN HS HJ SHOK HPM EXVD_Bspan; [exvd_awr_b (exv_s1 E) E9|]. exvd_step (exv_s1 E) E9 HMacc HGacc.
psrr_branch_tok RUN BR HS SHOK EXVD_Bspan; exvd_brl c E34 Hc.
- (* 109 < c *)
  apply Z.ltb_lt in Hc. rename Hc into Hg109.
  paj_run_tok_x_inv RUN HS HJ SHOK HPM EXVD_Bspan; [exvd_awr_b (exv_s1 E) E9|]. exvd_step (exv_s1 E) E9 HMacc HGacc.
  psrr_branch_tok RUN BR HS SHOK EXVD_Bspan; exvd_brl c E34 Hc.
  + (* 'n' *) apply Z.eqb_eq in Hc.
    paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM EXVD_Bspan (EXVD_EV0 + 0x42c); [exvd_awr_b (exv_s1 E) E9|].
    exvd_step (exv_s1 E) E9 HMacc HGacc.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ [2; 3; 4; 8; 9; 18; 19; 24; 25; 26]%bv HS
      ltac:(first [exact HAE | env_agree_chain HAE]) ltac:(vm_compute; reflexivity)) as HK;
    cbn [ms_regs restrict] in HK;
    destruct (exvd_lfin E lyc Sc Hpc Wc regs memc mdc k pos _ _ _ _ _ HP HB Hcur H27 HS ltac:(vm_compute; reflexivity)
      ltac:(exvd_ew E9) ltac:(exvd_ew E19) ltac:(exvd_ew E25) ltac:(exvd_ew E27) HJ HMacc HGacc HPM HK)
      as (HB' & Hcur' & SP144 & SP152);
    prreg HS (10%bv : bv 5) N10; prreg HS (11%bv : bv 5) N11; prreg HS (12%bv : bv 5) N12;
    pmkst HS; exvd_cfg_to 0x42c;
    eapply (WORD fx E lyc Sc Hpc Wc _ _ _ _ pos c _ _ _ _ Hn HP HB' Hcur' ltac:(unfold exv_len; zl) eq_refl);
    [ | rewrite N10; exvd_ew E19
      | rewrite N11; rewrite (HEI 243%nat ltac:(cbv; lia)); unfold w64; f_equal; vm_compute; reflexivity
      | rewrite N12; reflexivity
      | exact SP152 ];
    unfold exvd_lit; first [ left; repeat split; zl | right; left; repeat split; zl | right; right; repeat split; zl ].
  + apply Z.eqb_neq in Hc. rename Hc into Hn110.
    paj_run_tok_x_inv RUN HS HJ SHOK HPM EXVD_Bspan; [exvd_awr_b (exv_s1 E) E9|]. exvd_step (exv_s1 E) E9 HMacc HGacc.
    psrr_branch_tok RUN BR HS SHOK EXVD_Bspan; exvd_brl c E34 Hc.
    * (* 't' *) apply Z.eqb_eq in Hc.
      paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM EXVD_Bspan (EXVD_EV0 + 0x42c); [exvd_awr_b (exv_s1 E) E9|].
      exvd_step (exv_s1 E) E9 HMacc HGacc.
      pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ [2; 3; 4; 8; 9; 18; 19; 24; 25; 26]%bv HS
      ltac:(first [exact HAE | env_agree_chain HAE]) ltac:(vm_compute; reflexivity)) as HK;
    cbn [ms_regs restrict] in HK;
    destruct (exvd_lfin E lyc Sc Hpc Wc regs memc mdc k pos _ _ _ _ _ HP HB Hcur H27 HS ltac:(vm_compute; reflexivity)
      ltac:(exvd_ew E9) ltac:(exvd_ew E19) ltac:(exvd_ew E25) ltac:(exvd_ew E27) HJ HMacc HGacc HPM HK)
      as (HB' & Hcur' & SP144 & SP152);
    prreg HS (10%bv : bv 5) N10; prreg HS (11%bv : bv 5) N11; prreg HS (12%bv : bv 5) N12;
    pmkst HS; exvd_cfg_to 0x42c;
    eapply (WORD fx E lyc Sc Hpc Wc _ _ _ _ pos c _ _ _ _ Hn HP HB' Hcur' ltac:(unfold exv_len; zl) eq_refl);
    [ | rewrite N10; exvd_ew E19
      | rewrite N11; rewrite (HEI 243%nat ltac:(cbv; lia)); unfold w64; f_equal; vm_compute; reflexivity
      | rewrite N12; reflexivity
      | exact SP152 ];
    unfold exvd_lit; first [ left; repeat split; zl | right; left; repeat split; zl | right; right; repeat split; zl ].
    * apply Z.eqb_neq in Hc. rename Hc into Hn116.
      paj_run_tok_x_inv RUN HS HJ SHOK HPM EXVD_Bspan; [exvd_awr_b (exv_s1 E) E9|]. exvd_step (exv_s1 E) E9 HMacc HGacc.
      psrr_branch_tok RUN BR HS SHOK EXVD_Bspan; exvd_brl c E34 Hc.
      -- (* a number *) apply negb_true_iff, Z.eqb_neq in Hc. rename Hc into Hn123.
         paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM EXVD_Bspan (EXVD_EV0 + 0x278); [exvd_awr_b (exv_s1 E) E9|].
         exvd_step (exv_s1 E) E9 HMacc HGacc.
         pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ [2; 3; 4; 8; 9; 18; 19; 24; 25; 26]%bv HS
      ltac:(first [exact HAE | env_agree_chain HAE]) ltac:(vm_compute; reflexivity)) as HK;
    cbn [ms_regs restrict] in HK;
    destruct (exvd_lfin E lyc Sc Hpc Wc regs memc mdc k pos _ _ _ _ _ HP HB Hcur H27 HS ltac:(vm_compute; reflexivity)
      ltac:(exvd_ew E9) ltac:(exvd_ew E19) ltac:(exvd_ew E25) ltac:(exvd_ew E27) HJ HMacc HGacc HPM HK)
      as (HB' & Hcur' & SP144 & SP152);
    prreg HS (11%bv : bv 5) N11; prreg HS (12%bv : bv 5) N12; prreg HS (27%bv : bv 5) N27;
    exvd_shq HS (20%bv : bv 5) 19%nat 0 E19 E25 N20;
    pmkst HS; exvd_cfg_to 0x278;
    apply (CN fx E lyc Sc Hpc Wc _ _ _ _ pos c Hn HP HB' Hcur' ltac:(unfold exv_len; zl) eq_refl);
    [ unfold exv_disp; repeat match goal with |- context [?a =? ?b] => destruct (Z.eqb_spec a b); [zl|] end; reflexivity
    | rewrite N11; exvd_ew E32
    | rewrite N12; unfold exv_len; exvd_ew E33
    | rewrite N27; exvd_ew E34
    | rewrite N20; unfold w64, shadow_addr; rewrite Z.add_0_r; reflexivity
    | exact SP144 | exact SP152 ].
      -- (* '{' *) apply negb_false_iff, Z.eqb_eq in Hc.
         paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM EXVD_Bspan (EXVD_EV0 + 0x374); [exvd_awr_b (exv_s1 E) E9|].
         exvd_step (exv_s1 E) E9 HMacc HGacc.
         pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ [2; 3; 4; 8; 9; 18; 19; 24; 25; 26]%bv HS
      ltac:(first [exact HAE | env_agree_chain HAE]) ltac:(vm_compute; reflexivity)) as HK;
    cbn [ms_regs restrict] in HK;
    destruct (exvd_lfin E lyc Sc Hpc Wc regs memc mdc k pos _ _ _ _ _ HP HB Hcur H27 HS ltac:(vm_compute; reflexivity)
      ltac:(exvd_ew E9) ltac:(exvd_ew E19) ltac:(exvd_ew E25) ltac:(exvd_ew E27) HJ HMacc HGacc HPM HK)
      as (HB' & Hcur' & SP144 & SP152);
    prreg HS (10%bv : bv 5) N10; prreg HS (11%bv : bv 5) N11; prreg HS (27%bv : bv 5) N27; prreg HS (21%bv : bv 5) N21;
    prreg HS (23%bv : bv 5) N23;
    exvd_shq HS (20%bv : bv 5) 19%nat 0 E19 E25 N20;
    exvd_shq HS (22%bv : bv 5) 19%nat 8 E19 E25 N22;
    pmkst HS; exvd_cfg_to 0x374;
    apply (CI fx E lyc Sc Hpc Wc _ _ _ _ pos c Hn HP HB' Hcur' ltac:(unfold exv_len; zl) eq_refl);
    [ zl
    | rewrite N10; subst c; first [rewrite Hc | idtac]; reflexivity
    | rewrite N11; exvd_ew E32
    | rewrite N27; exvd_ew E34
    | rewrite N21; apply bv_eq; reflexivity
    | rewrite N20; unfold w64, shadow_addr; rewrite Z.add_0_r; reflexivity
    | rewrite N22; unfold w64, shadow_addr; reflexivity
    | rewrite N23; cbn [ew ewset Nat.eqb]; rewrite E19; unfold w64; f_equal; rewrite unsigned_lit_small by zl; reflexivity
    | exact SP144 | exact SP152 ].
- (* c <= 109 *)
  apply Z.ltb_ge in Hc. rename Hc into Hl109.
  paj_run_tok_x_inv RUN HS HJ SHOK HPM EXVD_Bspan; [exvd_awr_b (exv_s1 E) E9|]. exvd_step (exv_s1 E) E9 HMacc HGacc.
  psrr_branch_tok RUN BR HS SHOK EXVD_Bspan; exvd_brl c E34 Hc.
  + (* the quote *) apply Z.eqb_eq in Hc.
    paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM EXVD_Bspan (EXVD_EV0 + 0x1d0); [exvd_awr_b (exv_s1 E) E9|].
    exvd_step (exv_s1 E) E9 HMacc HGacc.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ [2; 3; 4; 8; 9; 18; 19; 24; 25; 26]%bv HS
      ltac:(first [exact HAE | env_agree_chain HAE]) ltac:(vm_compute; reflexivity)) as HK;
    cbn [ms_regs restrict] in HK;
    destruct (exvd_lfin E lyc Sc Hpc Wc regs memc mdc k pos _ _ _ _ _ HP HB Hcur H27 HS ltac:(vm_compute; reflexivity)
      ltac:(exvd_ew E9) ltac:(exvd_ew E19) ltac:(exvd_ew E25) ltac:(exvd_ew E27) HJ HMacc HGacc HPM HK)
      as (HB' & Hcur' & SP144 & SP152);
    prreg HS (21%bv : bv 5) N21;
    pmkst HS; exvd_cfg_to 0x1d0;
    apply (STR fx E lyc Sc Hpc Wc _ _ _ _ pos Hn HP HB' Hcur' ltac:(unfold exv_len; zl) Hc);
    [ rewrite N21; apply bv_eq; reflexivity | exact SP152 ].
  + apply Z.eqb_neq in Hc. rename Hc into Hn34.
    paj_run_tok_x_inv RUN HS HJ SHOK HPM EXVD_Bspan; [exvd_awr_b (exv_s1 E) E9|]. exvd_step (exv_s1 E) E9 HMacc HGacc.
    psrr_branch_tok RUN BR HS SHOK EXVD_Bspan; exvd_brl c E34 Hc.
    * (* '[' *) apply Z.eqb_eq in Hc.
      paj_run_tok_x_inv RUN HS HJ SHOK HPM EXVD_Bspan; [exvd_awr_b (exv_s1 E) E9|]. exvd_step (exv_s1 E) E9 HMacc HGacc.
      psrr_branch_tok RUN BR HS SHOK EXVD_Bspan; exvd_brl c E34 Hc0.
      -- exfalso. apply Z.eqb_eq in Hc0. zl.
      -- clear Hc0.
         paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM EXVD_Bspan (EXVD_EV0 + 0x374); [exvd_awr_b (exv_s1 E) E9|].
         exvd_step (exv_s1 E) E9 HMacc HGacc.
         pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ [2; 3; 4; 8; 9; 18; 19; 24; 25; 26]%bv HS
      ltac:(first [exact HAE | env_agree_chain HAE]) ltac:(vm_compute; reflexivity)) as HK;
    cbn [ms_regs restrict] in HK;
    destruct (exvd_lfin E lyc Sc Hpc Wc regs memc mdc k pos _ _ _ _ _ HP HB Hcur H27 HS ltac:(vm_compute; reflexivity)
      ltac:(exvd_ew E9) ltac:(exvd_ew E19) ltac:(exvd_ew E25) ltac:(exvd_ew E27) HJ HMacc HGacc HPM HK)
      as (HB' & Hcur' & SP144 & SP152);
    prreg HS (10%bv : bv 5) N10; prreg HS (11%bv : bv 5) N11; prreg HS (27%bv : bv 5) N27; prreg HS (21%bv : bv 5) N21;
    prreg HS (23%bv : bv 5) N23;
    exvd_shq HS (20%bv : bv 5) 19%nat 0 E19 E25 N20;
    exvd_shq HS (22%bv : bv 5) 19%nat 8 E19 E25 N22;
    pmkst HS; exvd_cfg_to 0x374;
    apply (CI fx E lyc Sc Hpc Wc _ _ _ _ pos c Hn HP HB' Hcur' ltac:(unfold exv_len; zl) eq_refl);
    [ zl
    | rewrite N10; subst c; first [rewrite Hc | idtac]; reflexivity
    | rewrite N11; exvd_ew E32
    | rewrite N27; exvd_ew E34
    | rewrite N21; apply bv_eq; reflexivity
    | rewrite N20; unfold w64, shadow_addr; rewrite Z.add_0_r; reflexivity
    | rewrite N22; unfold w64, shadow_addr; reflexivity
    | rewrite N23; cbn [ew ewset Nat.eqb]; rewrite E19; unfold w64; f_equal; rewrite unsigned_lit_small by zl; reflexivity
    | exact SP144 | exact SP152 ].
    * apply Z.eqb_neq in Hc. rename Hc into Hn91.
      paj_run_tok_x_inv RUN HS HJ SHOK HPM EXVD_Bspan; [exvd_awr_b (exv_s1 E) E9|]. exvd_step (exv_s1 E) E9 HMacc HGacc.
      psrr_branch_tok RUN BR HS SHOK EXVD_Bspan; exvd_brl c E34 Hc.
      -- (* a number *) apply negb_true_iff, Z.eqb_neq in Hc. rename Hc into Hn102.
         paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM EXVD_Bspan (EXVD_EV0 + 0x278); [exvd_awr_b (exv_s1 E) E9|].
         exvd_step (exv_s1 E) E9 HMacc HGacc.
         pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ [2; 3; 4; 8; 9; 18; 19; 24; 25; 26]%bv HS
      ltac:(first [exact HAE | env_agree_chain HAE]) ltac:(vm_compute; reflexivity)) as HK;
    cbn [ms_regs restrict] in HK;
    destruct (exvd_lfin E lyc Sc Hpc Wc regs memc mdc k pos _ _ _ _ _ HP HB Hcur H27 HS ltac:(vm_compute; reflexivity)
      ltac:(exvd_ew E9) ltac:(exvd_ew E19) ltac:(exvd_ew E25) ltac:(exvd_ew E27) HJ HMacc HGacc HPM HK)
      as (HB' & Hcur' & SP144 & SP152);
    prreg HS (11%bv : bv 5) N11; prreg HS (12%bv : bv 5) N12; prreg HS (27%bv : bv 5) N27;
    exvd_shq HS (20%bv : bv 5) 19%nat 0 E19 E25 N20;
    pmkst HS; exvd_cfg_to 0x278;
    apply (CN fx E lyc Sc Hpc Wc _ _ _ _ pos c Hn HP HB' Hcur' ltac:(unfold exv_len; zl) eq_refl);
    [ unfold exv_disp; repeat match goal with |- context [?a =? ?b] => destruct (Z.eqb_spec a b); [zl|] end; reflexivity
    | rewrite N11; exvd_ew E32
    | rewrite N12; unfold exv_len; exvd_ew E33
    | rewrite N27; exvd_ew E34
    | rewrite N20; unfold w64, shadow_addr; rewrite Z.add_0_r; reflexivity
    | exact SP144 | exact SP152 ].
      -- (* 'f' *) apply negb_false_iff, Z.eqb_eq in Hc.
         paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM EXVD_Bspan (EXVD_EV0 + 0x42c); [exvd_awr_b (exv_s1 E) E9|].
         exvd_step (exv_s1 E) E9 HMacc HGacc.
         pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ [2; 3; 4; 8; 9; 18; 19; 24; 25; 26]%bv HS
      ltac:(first [exact HAE | env_agree_chain HAE]) ltac:(vm_compute; reflexivity)) as HK;
    cbn [ms_regs restrict] in HK;
    destruct (exvd_lfin E lyc Sc Hpc Wc regs memc mdc k pos _ _ _ _ _ HP HB Hcur H27 HS ltac:(vm_compute; reflexivity)
      ltac:(exvd_ew E9) ltac:(exvd_ew E19) ltac:(exvd_ew E25) ltac:(exvd_ew E27) HJ HMacc HGacc HPM HK)
      as (HB' & Hcur' & SP144 & SP152);
    prreg HS (10%bv : bv 5) N10; prreg HS (11%bv : bv 5) N11; prreg HS (12%bv : bv 5) N12;
    pmkst HS; exvd_cfg_to 0x42c;
    eapply (WORD fx E lyc Sc Hpc Wc _ _ _ _ pos c _ _ _ _ Hn HP HB' Hcur' ltac:(unfold exv_len; zl) eq_refl);
    [ | rewrite N10; exvd_ew E19
      | rewrite N11; rewrite (HEI 243%nat ltac:(cbv; lia)); unfold w64; f_equal; vm_compute; reflexivity
      | rewrite N12; reflexivity
      | exact SP152 ];
    unfold exvd_lit; first [ left; repeat split; zl | right; left; repeat split; zl | right; right; repeat split; zl ].
Qed.

(* ---- the dispatch from CUT_C1: the end of the text or a byte ---- *)
Lemma exvd_c1 : forall n,
  (forall fy : YK11.FPState, CUT_CX (fx := fy) B ARx SK n) ->
  (forall fy : YK11.FPState, CUT_CN (fx := fy) B ARx SK n) -> (forall fy : YK11.FPState, CUT_CI (fx := fy) B ARx SK n) ->
  (forall fy : YK11.FPState, EXVD_STR (fx := fy) B ARx SK n) -> (forall fy : YK11.FPState, EXVD_WORD (fx := fy) B ARx SK n) ->
  CUT_C1 (fx := fx) B ARx SK n.
Proof.
intros n CX CN CI STR WORD. unfold CUT_C1.
intros E lyc Sc Hpc Wc regs memc mdc k pos Hn HP HB Hcur H27.
destruct (Z_lt_le_dec (exv_i1 E) (exv_len E)) as [Hl | Hl].
- exact (exvd_c1_byte n E lyc Sc Hpc Wc regs memc mdc k pos CN CI STR WORD Hn HP HB Hcur H27 Hl).
- exact (exvd_c1_end n E lyc Sc Hpc Wc regs memc mdc k pos CX Hn HP HB Hcur Hl).
Qed.

End r.

(* at every float state *)
Lemma exvd_c1_all : forall {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive} B ARx SK,
  EXV_HYP B ARx SK -> forall n,
  (forall fy : YK11.FPState, CUT_CX (fx := fy) B ARx SK n) ->
  (forall fy : YK11.FPState, CUT_CN (fx := fy) B ARx SK n) -> (forall fy : YK11.FPState, CUT_CI (fx := fy) B ARx SK n) ->
  (forall fy : YK11.FPState, EXVD_STR (fx := fy) B ARx SK n) -> (forall fy : YK11.FPState, EXVD_WORD (fx := fy) B ARx SK n) ->
  forall fx : YK11.FPState, CUT_C1 (fx := fx) B ARx SK n.
Proof. intros rc ci cp RL B ARx SK HYP n CX CN CI STR WORD fx. exact (exvd_c1 (fx := fx) B ARx SK HYP n CX CN CI STR WORD). Qed.

Print Assumptions exvd_c1_all.
