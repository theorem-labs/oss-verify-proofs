(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Rebound onto the old-pin kit (base cold/h-rw-pre-7-b-ex_value-rebind 88c5348fe7fc, kit 4f18c75d4900): the post is
   fpostWFm; its memnorm keep comes from EXB's exv_rm keep and exx_memnorm_keep across the run (the run writes only bytes
   the cut's memory defines), its room from exv_room_free. Does not rest on tex_word_specX; makes no call. *)
(* Theorem Labs, 2026-10: fuzz_preset, image B (asan-ubsan), ex_value: SEGMENT CX (EXIT) of the walk, B 0x83fa8
   (exv_pc 0xa7c) .. the `ret` at B 0x84078. Proves no function: the segment lemma `exvB_exit` is ExvB_Top.v's
   Section hypothesis `seg_exit`, with EXV_HYP as a premise.
   THE CODE (neutral listing, the internal file ex_value.fuzz_preset.asan-ubsan.s, a Theorem Labs lane's listing of the B' pin, rows 673-725):
   the frame's retire word (`sd a0, 0(s2)`, the magic 0x45e0360e), `beqz s8` (s8 = the frame, nonzero: NOT taken, so
   the zero-shadow arm B 0x84008 is unreachable), the sixteen 0xf5 shadow bytes of the class-1 frame (s10 + 0 .. 15),
   the INLINE RELEASE (`ld a0, 120(s8)`; `sb zero, 0(a0)`: the flag byte := 0), `mv a0, s5`, and the epilogue
   (sp = s0 - 288, ra and s0 .. s11 from their slots, sp += 288, `ret`).
   THE RUN is ONE symbolic run of the listing engine (YC80x / YC1fPx over YCbqG's ajournal_x) under YGcallSx.v's
   aj_flag_store_x, which turns the journal's own frame list [(1, pos)] into [] at stack_free_state 1 pos; then
   YC1fP's paj_ret_at. No UBSan check lies in the segment; no ASan check either (the stores are the frame's own).
   Numerals: 0xa7c (DERIVED: B 0x83fa8 minus B's ex_value entry, both the internal file neutral_dis.py); 288 (LENGTH: the frame,
   `addi sp, sp, -288`); 104, 8 (LENGTH: the thirteen saved words below the entry sp, a word); 120 (LENGTH: the flag
   word's offset in the class-1 frame, fs_frame_bytes 1 - 8); 128, 16 (LENGTH: the class-1 frame and its shadow
   bytes); 304 (LENGTH: pi_frame F_ex_value at prh_img_B, read by computation); 4096, 2 ^ 46, 2 ^ 47, 2 ^ 64, 256
   (LENGTH / DERIVED: address-space and byte bounds); 32, 5 (LENGTH: the frame's alignment, its exponent);
   400 (LENGTH: the run's fuel); 512 (DERIVED: run_K at A_LIM); 3 (DERIVED: the flag region's index in the final
   symbolic state); 0 .. 12 (DERIVED: the saved-word index into exv_saved); register numbers 1, 2, 3, 4, 8, 9, 10,
   18 .. 27 (WORD); atom numbers 8, 18, 21, 24, 26, 32 .. 45 (DERIVED: the symbolic engine's numbering - 0 .. 31
   the registers, 32 the flag address, 33 .. 45 the saved words). No ADDRESS literal: the segment's pc is
   B_prog_sigma AS_ex_value - B_prog_base + 0xa7c.
   THE LEDGER after the release: the statics are image bytes (S1ImgB.pst_in_img_B), the frame, its shadow and the
   flag are not (frm_img_x, the shadow band, eh_fflx); a harness head word lies inside its block (EXV_HYP's MARKED
   eh_head: 8 <= cf_head), which the frame misses (sep_block_frame_x), the shadow band misses (in_app) and the flag,
   runtime-owned, misses (alx_blocks). The room: EXV_HYP's MARKED room_live_free. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcallx YGcallSx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_FnEx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import PRH_ImgB Img0 Listing_prog PAImg_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import ExvB_Stmt S1ImgB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

#[local] Existing Instance prh_img_B.

(* ---- the symbolic state at the cut (B 0x83fa8) ----
   Atoms 0 .. 31 are the registers at the cut (sr_atoms), with s8 (24) written as the atom of s2 (18): both hold the
   frame, and the code stores through s2 and loads / branches through s8. Atom 32 is the flag address (the word at
   frame + 120); atoms 33 .. 45 are the thirteen words the prologue spilled (ra, s0, s1, s2 .. s11 at entry, the order
   of exv_saved). The four regions: the saved block below the entry sp (read only, through s0 = the entry sp), the
   frame (its first word written, the flag word read), its sixteen shadow bytes (through s10), the flag byte. The
   facts give each written region's base a range (the engine's cell check needs one) and the frame its alignment, so
   the engine decides `beqz s8` itself and the segment is ONE run to `ret`. *)
Definition EXX_OFF : Z := 0xa7c.
Definition EXX_PC : Z := B_prog_sigma AS_ex_value - B_prog_base + EXX_OFF.
Definition exx_saved_regs : list (bv 5) := map (fun p => Z_to_bv 5 (snd p)) exv_saved.
Definition exx_chunk (j : nat) : YP09.chunk :=
  YP09.mkChunk (fst (nth j exv_saved (0, 0)) - 288) (CVal 8 (SOff (33 + j) 0)).
Definition exx_saved_chunks : list YP09.chunk := map exx_chunk (seq 0 13).
Definition exx_regions : smem :=
  [ YP09.mkRegion (Some 8%nat) (-104) 0 0 0 exx_saved_chunks;
    YP09.mkRegion (Some 18%nat) 0 128 0 8 [YP09.mkChunk 120 (CVal 8 (SOff 32%nat 0))];
    YP09.mkRegion (Some 26%nat) 0 16 0 16 [];
    YP09.mkRegion (Some 32%nat) 0 1 0 1 [] ].
Definition exx_facts : facts :=
  mkFacts [(18%nat, mkAF 4096 (2 ^ 47) 5); (26%nat, mkAF SHADOW_OFF (2 ^ 46) 0); (32%nat, mkAF 4096 (2 ^ 47) 0)] [] [].
Definition exx_sr : list sv := sr_set sr_atoms 24%bv (SOff 18 0).
Definition ss_exx : sstate := mkSS EXX_PC exx_sr exx_regions None exx_facts.
Definition exx_Bx : sv := SLit 0.
Definition exx_Bspan : Z * Z := (0, 0).
Definition exx_SH : list shent := [].

Lemma exx_zmaxl_nonneg : forall l, 0 <= zmaxl l.
Proof. induction l as [|a l IH]; cbn [zmaxl fold_right]; [lia|]. unfold zmaxl in IH. lia. Qed.
(* the walk's stack need is at least the frame: 304 = pi_frame F_ex_value at prh_img_B *)
Lemma exx_stk_ge : forall n, 304 <= STK_ex_value (PI := prh_img_B) n.
Proof.
intros n. unfold STK_ex_value. change (@pi_frame prh_img_B F_ex_value) with 304.
pose proof (exx_zmaxl_nonneg [STK_RT_ECALL; STK_RT_STR; STK_RT_STRTOD; STK_ex_string; STK_ex_word; STK_ex_ws]). lia.
Qed.
Lemma exx_fb1 : fs_frame_bytes 1 = 128.
Proof. reflexivity. Qed.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
#[local] Notation VAL := (@pa_val _ B_prog_listing PI_prog_B).
#[local] Notation BASE := (@pa_val _ B_prog_listing PI_prog_B A_TEXT).
#[local] Notation PST := (@prh_pst prh_img_B).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world rsegs -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
Hypothesis HYP : EXV_HYP B ARx SK.

Definition exx_E (regs regs0 : bvmap 5 word) (fl : Z) : env :=
  @Eimg _ B_prog_listing PI_prog_B (Ereg regs (w64 fl :: map (getr regs0) exx_saved_regs)).

Lemma exx_E_low : forall regs regs0 fl n, (n < A_TEXT)%nat ->
  ew (exx_E regs regs0 fl) n = ew (Ereg regs (w64 fl :: map (getr regs0) exx_saved_regs)) n.
Proof. intros regs regs0 fl n Hn. unfold exx_E. apply Eimg_low. exact Hn. Qed.
Lemma exx_E_reg : forall regs regs0 fl (r : bv 5) n, Z.of_nat n = bv_unsigned r ->
  ew (exx_E regs regs0 fl) n = getr regs r.
Proof.
intros regs regs0 fl r n Hn. pose proof (bv_unsigned_in_range 5 r) as R. change (bv_modulus 5) with 32 in R.
rewrite exx_E_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn.
Qed.
Lemma exx_E_fl : forall regs regs0 fl, ew (exx_E regs regs0 fl) 32 = w64 fl.
Proof. intros. rewrite exx_E_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 0). Qed.
Lemma exx_E_saved : forall regs regs0 fl j, (j < 13)%nat ->
  ew (exx_E regs regs0 fl) (33 + j) = getr regs0 (Z_to_bv 5 (snd (nth j exv_saved (0, 0)))).
Proof.
intros regs regs0 fl j Hj. rewrite exx_E_low by (unfold A_TEXT; lia).
replace (33 + j)%nat with (32 + S j)%nat by lia. rewrite ew_Ereg_extra. cbn [nth].
unfold exx_saved_regs. rewrite map_map.
rewrite (nth_indep _ _ ((fun p : Z * Z => getr regs0 (Z_to_bv 5 (snd p))) (0, 0))) by (rewrite length_map; cbn; lia).
exact (map_nth (fun p : Z * Z => getr regs0 (Z_to_bv 5 (snd p))) exv_saved (0, 0) j).
Qed.

(* ---- the entry symbolic state of the segment ---- *)
Lemma exx_entry : forall (ly : alayout) (S : astate) (Hp : list Z) (W : world rsegs)
  (regs regs0 : bvmap 5 word) (mem : word -> option byte) (md : Model) (pos : Z),
  ARx ly S Hp W mem md -> In (1, pos) (frames S) ->
  getr regs 8 = w64 (spZ regs0) ->
  getr regs 18 = w64 (frame_addr ly 1 pos) -> getr regs 24 = w64 (frame_addr ly 1 pos) ->
  getr regs 26 = w64 (shadow_addr (frame_addr ly 1 pos)) ->
  (forall o r, In (o, r) exv_saved ->
     val_mem rsegs (rdW W mem) (spZ regs0 - 288 + o) 8 (bv_unsigned (getr regs0 (Z_to_bv 5 r)))) ->
  rdword (aview rsegs (w_H W) mem) (frame_addr ly 1 pos + 120) = Some (flag_addr ly 1 pos) ->
  alloc_ceiling + 104 <= spZ regs0 ->
  st_ok_pi rsegs VAL (exx_E regs regs0 (flag_addr ly 1 pos)) ss_exx
    (restrict (w_H W) (YK11.mkst regs (Z_to_bv 64 (BASE + EXX_PC)) mem (YK11.seg_rom rsegs)))
  /\ sh_ok rsegs exx_Bx exx_SH (exx_E regs regs0 (flag_addr ly 1 pos)) (rdW W mem).
Proof.
intros ly S Hp W regs regs0 mem md pos HAR Hin H8 H18 H24 H26 HSAV HFLW Hlo.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (eh_laws B ARx SK HYP) as LAWS.
destruct (alx_frames _ _ _ LAWS ly S Hp W mem md 1 pos HAR Hin) as (Hmod & Happ & Hfpres & Hshpres).
destruct (eh_fflx B ARx SK HYP ly S Hp W mem md 1 pos HAR Hin) as (Hflpres & Hflown & (Hflapp & Hflimg) & (Hfl4096 & Hflz2 & Hflceil)).
destruct (frames_bounds_x rsegs B ARx LAWS ly S Hp W mem md 1 pos HAR Hin) as (HF4096 & HFceil & _).
rewrite exx_fb1 in Happ, Hfpres, Hshpres, HFceil. change (128 / 8) with 16 in Hshpres.
rewrite restrict_mkst_fx.
set (fl := flag_addr ly 1 pos) in *.
set (F := frame_addr ly 1 pos) in *.
set (E := exx_E regs regs0 fl).
assert (Hsp64 : 0 <= spZ regs0 < 2 ^ 64) by (unfold spZ; apply u64_range).
assert (Usp : bv_unsigned (ew E 8) = spZ regs0)
  by (unfold E; rewrite (exx_E_reg regs regs0 fl 8%bv 8) by reflexivity; rewrite H8; unfold w64; apply unsigned_lit_small; lia).
assert (UF : bv_unsigned (ew E 18) = F)
  by (unfold E; rewrite (exx_E_reg regs regs0 fl 18%bv 18) by reflexivity; rewrite H18; unfold w64; apply unsigned_lit_small; lia).
pose proof (Z.div_pos F 8 ltac:(lia) ltac:(lia)) as HF8p.
assert (HF8 : F / 8 <= F) by (apply Z.div_le_upper_bound; lia).
assert (USH : bv_unsigned (ew E 26) = shadow_addr F).
{ unfold E; rewrite (exx_E_reg regs regs0 fl 26%bv 26) by reflexivity; rewrite H26; unfold w64.
  apply unsigned_lit_small. unfold shadow_addr, SHADOW_OFF. lia. }
assert (UFL : bv_unsigned (ew E 32) = fl)
  by (unfold E; rewrite exx_E_fl; unfold w64; apply unsigned_lit_small; lia).
(* the frame's shadow bytes lie in the shadow band, apart from the frame (in_app's two cases) *)
assert (HSB : F + 128 <= shadow_addr F \/ shadow_addr F + 16 <= F).
{ unfold shadow_addr. destruct Happ as (_ & [HL | (HH1 & HH2)]).
  - left. unfold SHADOW_OFF, kLowShadowBeg in *. lia.
  - right. unfold SHADOW_OFF, kHighMemBeg in *. lia. }
assert (HSHhi : shadow_addr F + 16 <= 2 ^ 46) by (unfold shadow_addr, SHADOW_OFF; lia).
(* the flag is runtime-owned and no byte of the frame or of its shadow is *)
assert (HflF : fl < F \/ F + 128 <= fl).
{ destruct (Z_lt_le_dec fl F) as [h|h]; [left; exact h|].
  destruct (Z_lt_le_dec fl (F + 128)) as [h2|h2]; [|right; exact h2].
  exfalso. exact (proj2 (Hfpres fl (conj h h2)) Hflown). }
assert (HflSH : fl < shadow_addr F \/ shadow_addr F + 16 <= fl).
{ destruct (Z_lt_le_dec fl (shadow_addr F)) as [h|h]; [left; exact h|].
  destruct (Z_lt_le_dec fl (shadow_addr F + 16)) as [h2|h2]; [|right; exact h2].
  exfalso. pose proof (proj2 (Hshpres (fl - shadow_addr F) ltac:(lia))) as Hno.
  replace (shadow_addr F + (fl - shadow_addr F)) with fl in Hno by lia. exact (Hno Hflown). }
split.
- unfold ss_exx. apply (pa_entry_st_ok_full (fx := fx) (L := B_prog_listing) (PI := PI_prog_B)).
  + unfold exx_sr. apply regs_ok_pin; [apply regs_ok_Eimg_Ereg | intros X; discriminate X |].
    cbn [sv_denot]. fold E. rewrite UF, Z.add_0_r, H24. reflexivity.
  + vm_compute. reflexivity.
  + unfold exx_regions.
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]].
    * unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite Usp. split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|].
      unfold exx_saved_chunks. apply Forall_forall. intros c Hc. apply in_map_iff in Hc as (j & <- & Hj).
      apply in_seq in Hj. destruct Hj as [_ Hj]. cbn [Nat.add] in Hj.
      destruct (nth j exv_saved (0, 0)) as [o rr] eqn:Hor.
      assert (Hin' : In (o, rr) exv_saved) by (rewrite <- Hor; apply nth_In; cbn; lia).
      unfold exx_chunk. rewrite Hor. cbn [fst].
      eapply (chunk_ok_val rsegs E _ (spZ regs0) (o - 288) 8 _ (bv_unsigned (getr regs0 (Z_to_bv 5 rr)))).
      -- cbn [sv_denot]. unfold E. rewrite (exx_E_saved regs regs0 fl j Hj), Hor. cbn [snd].
         rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
      -- pose proof (u64_range (getr regs0 (Z_to_bv 5 rr))). zside.
      -- zside.
      -- replace (spZ regs0 + (o - 288)) with (spZ regs0 - 288 + o) by lia. exact (HSAV o rr Hin').
    * unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite UF. split; [lia|]. split; [lia|].
      split; [intros o Ho; apply apresent_writable; exact (proj1 (Hfpres (F + o) ltac:(lia)))|].
      apply Forall_cons; [|apply Forall_nil].
      eapply (chunk_ok_val rsegs E _ F 120 8 (SOff 32%nat 0) fl);
      [ cbn [sv_denot]; unfold E; rewrite exx_E_fl; unfold w64; rewrite Z.add_0_r, unsigned_lit_small by lia; reflexivity
      | zside | zside | exact (val_mem_of_rdword rsegs _ _ _ _ HFLW) ].
    * unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite USH. split; [unfold shadow_addr, SHADOW_OFF; lia|].
      split; [lia|]. split; [|apply Forall_nil].
      intros o Ho. apply apresent_writable. exact (proj1 (Hshpres o ltac:(lia))).
    * unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite UFL. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
      intros o Ho. replace (fl + o) with fl by lia. apply apresent_writable. exact Hflpres.
  + apply pairwise_disjoint_of_extents. unfold exx_regions, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite Usp, UF, USH, UFL.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold shadow_addr, SHADOW_OFF in *. repeat split; lia.
  + split; [|split; [exact I | exact I]].
    cbn [exx_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite UF, USH, UFL. change (2 ^ 5) with 32. rewrite Z.pow_0_r, Z.mod_1_r.
    unfold shadow_addr, SHADOW_OFF in *. repeat split; lia.
- unfold sh_ok, exx_SH. apply Forall_nil.
Qed.

(* ---- the run's write set: the frame's first word, its sixteen shadow bytes, the flag byte ---- *)
Lemma exx_wr : forall regs regs0 fl F a,
  getr regs 18 = w64 F -> getr regs 26 = w64 (shadow_addr F) -> 0 <= F -> F + 128 <= 2 ^ 47 -> 0 <= fl < 2 ^ 64 ->
  in_wrange (exx_E regs regs0 fl) exx_regions a ->
  (F <= a < F + 8) \/ (shadow_addr F <= a < shadow_addr F + 16) \/ a = fl.
Proof.
intros regs regs0 fl F a H18 H26 HF0 HF1 Hfl (rg & Hrg & Hr).
pose proof (Z.div_pos F 8 ltac:(lia) ltac:(lia)).
assert (F / 8 <= F) by (apply Z.div_le_upper_bound; lia).
unfold exx_regions in Hrg. destruct Hrg as [<- | [<- | [<- | [<- | []]]]];
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr.
- lia.
- rewrite (exx_E_reg regs regs0 fl 18%bv 18) in Hr by reflexivity. rewrite H18 in Hr. unfold w64 in Hr.
  rewrite unsigned_lit_small in Hr by lia. lia.
- rewrite (exx_E_reg regs regs0 fl 26%bv 26) in Hr by reflexivity. rewrite H26 in Hr. unfold w64 in Hr.
  rewrite unsigned_lit_small in Hr by (unfold shadow_addr, SHADOW_OFF; lia). lia.
- rewrite exx_E_fl in Hr. unfold w64 in Hr. rewrite unsigned_lit_small in Hr by lia. lia.
Qed.
Lemma exx_keep : forall (W : world rsegs) regs regs0 fl (m m' : word -> option byte) F,
  frame_of (exx_E regs regs0 fl) exx_regions (rdW W m) (rdW W m') ->
  getr regs 18 = w64 F -> getr regs 26 = w64 (shadow_addr F) -> 0 <= F -> F + 128 <= 2 ^ 47 -> 0 <= fl < 2 ^ 64 ->
  forall a, 0 <= a < 2 ^ 64 -> ~ (F <= a < F + 8) -> ~ (shadow_addr F <= a < shadow_addr F + 16) -> a <> fl ->
  aview rsegs (w_H W) m' a = aview rsegs (w_H W) m a.
Proof.
intros W regs regs0 fl m m' F HFr H18 H26 HF0 HF1 Hfl a Ha N1 N2 N3.
apply aview_eq_of. apply HFr. rewrite unsigned_lit_small by lia. intros Hw.
destruct (exx_wr regs regs0 fl F a H18 H26 HF0 HF1 Hfl Hw) as [H | [H | H]]; contradiction.
Qed.
(* a region of a final symbolic state, read back (ex_ws_x.v's exw_region_nth / exw_field, at st_ok_pi) *)
Lemma exx_region_nth : forall E ss ms i rg,
  st_ok_pi rsegs VAL E ss ms -> nth_error (ss_mem ss) i = Some rg -> region_ok rsegs E (ms_mem ms) rg.
Proof.
intros E ss ms i rg HS Hi. unfold st_ok_pi in HS. destruct (st_ok_mem_ok rsegs E _ ms HS) as (_ & Hrs & _).
destruct ss. exact (proj1 (Forall_forall _ _) Hrs rg (nth_error_In _ _ Hi)).
Qed.
Lemma exx_field : forall E m n b cs lo hi wlo whi od (w : N) e v,
  region_ok rsegs E m (YP09.mkRegion (Some n) lo hi wlo whi cs) ->
  bv_unsigned (ew E n) = b -> In (YP09.mkChunk od (CVal w e)) cs -> sv_denot E e = Z_to_bv 64 v ->
  0 <= v < 2 ^ (8 * Z.of_N w) -> (Z.of_N w <= 8) ->
  val_mem rsegs m (b + od) (N.to_nat w) v.
Proof.
intros E m n b cs lo hi wlo whi od w e v (_ & _ & _ & Hcs) Hn Hc He Hv Hw.
pose proof (proj1 (Forall_forall _ _) Hcs _ Hc) as Hck. cbn [YP09.r_base base_val] in Hck. rewrite Hn in Hck.
exact (val_of_chunk_ok rsegs E m b od w e v Hck He Hv Hw).
Qed.

(* ---- the ledger after the segment: its reads (the statics, image bytes; the harness heads, inside their blocks
   since cf_head >= 8) miss the frame's word, its shadow and the flag byte ---- *)
Lemma exx_ledger : forall ly S Hp (W : world rsegs) mem md mem' pos Lam peak cnt fail ran most own,
  ARx ly S Hp W mem md -> In (1, pos) (frames S) ->
  (forall a, 0 <= a < alloc_ceiling -> ~ (frame_addr ly 1 pos <= a < frame_addr ly 1 pos + 8) ->
     ~ (shadow_addr (frame_addr ly 1 pos) <= a < shadow_addr (frame_addr ly 1 pos) + 16) -> a <> flag_addr ly 1 pos ->
     aview rsegs (w_H W) mem' a = aview rsegs (w_H W) mem a) ->
  prh_ledger (PI := prh_img_B) (L := B_prog_listing) (PA := PI_prog_B) B ly S Hp W mem Lam peak cnt fail ran most own ->
  prh_ledger (PI := prh_img_B) (L := B_prog_listing) (PA := PI_prog_B) B ly (stack_free_state 1 pos S) Hp W mem'
    Lam peak cnt fail ran most own.
Proof.
intros ly S Hp W mem md mem' pos Lam peak cnt fail ran most own HAR Hin HK (HG & HND & HB & HP).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (eh_laws B ARx SK HYP) as LAWS.
destruct (eh_fflx B ARx SK HYP ly S Hp W mem md 1 pos HAR Hin) as (_ & Hflown & (_ & Hflimg) & (Hfl4096 & _ & Hflceil)).
destruct (frames_bounds_x rsegs B ARx LAWS ly S Hp W mem md 1 pos HAR Hin) as (HF4096 & HFceil & _).
rewrite exx_fb1 in HFceil.
pose proof (Z.div_pos (frame_addr ly 1 pos) 8 ltac:(lia) ltac:(lia)) as HF8.
assert (VK : forall a (w : nat) v, val_mem rsegs (rdW W mem) a w v ->
  (forall x, a <= x < a + Z.of_nat w -> aview rsegs (w_H W) mem' x = aview rsegs (w_H W) mem x) ->
  val_mem rsegs (rdW W mem') a w v).
{ intros a w v Hv HE kk Hk. rewrite (mbyte_of_aview rsegs (w_H W) (w_H W) mem mem' (a + Z.of_nat kk)); [exact (Hv kk Hk)|].
  apply HE. lia. }
assert (KS : forall x, Exists (in_zr x) (@prh_pst prh_img_B) -> aview rsegs (w_H W) mem' x = aview rsegs (w_H W) mem x).
{ intros x Hx. pose proof (pst_in_img_B x Hx) as Himg. pose proof (B_prog_segs_low x Himg) as Hlow.
  unfold kLowMemEnd in Hlow. apply HK.
  - lia.
  - intros Hf. apply (frm_img_x rsegs B ARx LAWS ly S Hp W mem md 1 pos x HAR Hin); [rewrite exx_fb1; lia | exact Himg].
  - unfold shadow_addr, SHADOW_OFF. lia.
  - intros E. rewrite E in Himg. exact (Hflimg Himg). }
unfold prh_ledger. split; [|split; [exact HND | split; [|exact HP]]].
- destruct HG as (VL & VP & VC & VF & VR & (VM & VMr) & (VO & VOr) & Hb).
  split; [apply (VK _ _ _ VL); intros x Hx; apply KS; unfold prh_pst; apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; exact Hx|].
  split; [apply (VK _ _ _ VP); intros x Hx; apply KS; unfold prh_pst; apply Exists_cons_tl, Exists_cons_hd; unfold in_zr; cbn [fst snd]; exact Hx|].
  split; [apply (VK _ _ _ VC); intros x Hx; apply KS; unfold prh_pst; do 2 apply Exists_cons_tl; apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; exact Hx|].
  split; [apply (VK _ _ _ VF); intros x Hx; apply KS; unfold prh_pst; do 3 apply Exists_cons_tl; apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; exact Hx|].
  split; [apply (VK _ _ _ VR); intros x Hx; apply KS; unfold prh_pst; do 4 apply Exists_cons_tl; apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; exact Hx|].
  split; [split; [apply (VK _ _ _ VM); intros x Hx; apply KS; unfold prh_pst; do 5 apply Exists_cons_tl; apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; exact Hx | exact VMr]|].
  split; [split; [apply (VK _ _ _ VO); intros x Hx; apply KS; unfold prh_pst; do 6 apply Exists_cons_tl; apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; exact Hx | exact VOr]|].
  exact Hb.
- revert HB. apply Forall_impl. intros [a kk] (K0 & Kin & Khp & Kal & Kv). cbn [fst snd] in *.
  refine (conj K0 (conj _ (conj Khp (conj Kal _)))).
  + unfold ablocks. rewrite blocks_stack_free_state. exact Kin.
  + apply (VK _ _ _ Kv). intros x Hx. change (Z.of_nat 8) with 8 in Hx.
    pose proof (eh_head B ARx SK HYP) as HH.
    destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md _ _ HAR Kin) as (B1 & B2 & B3 & Bapp & Bown & _).
    assert (Hreq : req_size (kk + cf_head) = kk + cf_head) by (unfold req_size; destruct (Z.eqb_spec (kk + cf_head) 0); lia).
    rewrite Hreq in B3, Bapp, Bown.
    assert (Hxb : a - cf_head <= x < a - cf_head + (kk + cf_head)) by lia.
    pose proof (sep_block_frame_x rsegs B ARx LAWS ly S Hp W mem md (a - cf_head) (kk + cf_head) 1 pos HAR Kin Hin) as Hsep.
    unfold zdisjoint in Hsep. cbn [fst snd] in Hsep. rewrite Hreq, exx_fb1 in Hsep.
    apply HK.
    * lia.
    * lia.
    * unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Bapp. unfold shadow_addr, SHADOW_OFF. lia.
    * intros E. rewrite E in Hxb. exact (proj2 (Bown _ Hxb) Hflown).
Qed.

(* YC1fP's prreg at image B's instance, passed explicitly (an inferred PAImg instance is the wrong listing's) *)
Ltac exx_reg HS r Hr :=
  lazymatch type of HS with
  | st_ok_pi _ _ ?E ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_pi_restrict_reg (L := B_prog_listing) (PI := PI_prog_B) H E ss ms r HS) as Hr;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
    cbn [ms_regs restrict mkst] in Hr; prreg_norm Hr
  end.

(* ---- memnorm across a stretch: the end memory equals the start one off a decidable write set whose every byte the
   start memory defines; memnorm reads only WHICH addresses are defined (YAkMemnorm.memnorm), so it is kept ---- *)
Lemma exx_memnorm_keep : forall (m m' : word -> option byte) (Wr : Z -> Prop),
  (forall a, {Wr a} + {~ Wr a}) ->
  (forall x : word, ~ Wr (bv_unsigned x) -> m' x = m x) ->
  (forall x : word, Wr (bv_unsigned x) -> exists b, m x = Some b) ->
  YAkMemnorm.memnorm rsegs m -> YAkMemnorm.memnorm rsegs m'.
Proof.
intros m m' Wr Hd Hfr Hw Hm. unfold YAkMemnorm.memnorm in Hm |- *. destruct Hm as (Hi & Ht).
split; intros x b E; destruct (Hd (bv_unsigned x)) as [h|h].
- destruct (Hw x h) as (b0 & E0). exact (Hi x b0 E0).
- rewrite (Hfr x h) in E. exact (Hi x b E).
- destruct (Hw x h) as (b0 & E0). exact (Ht x b0 E0).
- rewrite (Hfr x h) in E. exact (Ht x b E).
Qed.
Lemma exx_dec3 : forall F s fl a,
  {(F <= a < F + 8) \/ (s <= a < s + 16) \/ a = fl} + {~ ((F <= a < F + 8) \/ (s <= a < s + 16) \/ a = fl)}.
Proof.
intros F s fl a.
destruct (Z.eq_dec a fl) as [e|e]; [left; right; right; exact e|].
destruct (Z_lt_le_dec a F) as [h1|h1]; destruct (Z_lt_le_dec a (F + 8)) as [h2|h2];
destruct (Z_lt_le_dec a s) as [h3|h3]; destruct (Z_lt_le_dec a (s + 16)) as [h4|h4];
first [left; lia | right; lia].
Qed.

(* ---- THE SEGMENT ---- *)
Lemma exx_cut : forall n, CUT_CX (fx := fx) B ARx SK n.
Proof.
unfold CUT_CX. intros n X lyc Sc Hpc Wc regs memc mdc k pos r Hn HPRE HEXB H21 HRES.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (eh_laws B ARx SK HYP) as LAWS.
unfold EXV_PRE in HPRE. cbv zeta in HPRE.
destruct HPRE as ((HFN & HROD) & HPfrm & HPcnt & HP10 & HP11 & HPcur & HPq8 & HPch & HPq1 & HPq2 & HPwin & _).
pose proof HFN as (HAR0 & Hra & Hra4 & Hgp & Htp & Hastk0 & Hpres0 & Hch0 & HQT0).
destruct HPwin as (Hd0 & _).
unfold EXB in HEXB. cbv zeta in HEXB.
destruct HEXB as (HJ & HWIN & HFK & HFZ & HHp & HAB & HRK & HLED & HCNT & R2 & R8 & R9 & R18 & R24 & R25 & R26 & R19 &
  R3 & R4 & HSAV & H176 & HFLW & _).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & _ & Jastk & _ & _).
pose proof Jastk as (_ & _ & Jceil & Jslo & Jshi & J47 & _ & Jtop1 & Jtop2).
assert (Hin : In (1, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
pose proof (exx_stk_ge (e_n X)) as HSTK.
unfold exv_STK, exv_sp in Jslo, Jshi, Jtop1.
assert (Hsp : alloc_ceiling + 104 <= spZ (e_regs X)) by lia.
assert (Htop : spZ (e_regs X) + e_d X <= 2 ^ 47) by lia.
destruct (eh_fflx B ARx SK HYP lyc Sc Hpc Wc memc mdc 1 pos HAR Hin) as (Hflpres & Hflown & (_ & Hflimg) & (Hfl4096 & _ & Hflceil)).
destruct (alx_frames _ _ _ LAWS lyc Sc Hpc Wc memc mdc 1 pos HAR Hin) as (_ & _ & Hfpres & Hshpres).
rewrite exx_fb1 in Hfpres, Hshpres. change (128 / 8) with 16 in Hshpres.
destruct HRK as (HRM & HMN).
destruct (frames_bounds_x rsegs B ARx LAWS lyc Sc Hpc Wc memc mdc 1 pos HAR Hin) as (HF4096 & HFceil & _).
rewrite exx_fb1 in HFceil.
destruct (exx_entry lyc Sc Hpc Wc regs (e_regs X) memc mdc pos HAR Hin R8 R18 R24 R26 HSAV HFLW Hsp) as [HS SHOK].
remember (exx_E regs (e_regs X) (flag_addr lyc 1 pos)) as Ev eqn:HEv.
assert (HEI : img_env VAL A_LIM Ev) by (rewrite HEv; unfold exx_E; apply Eimg_env).
(* the atoms' values *)
assert (E21 : ew Ev 21 = w64 r) by (rewrite HEv, (exx_E_reg regs (e_regs X) _ 21%bv 21) by reflexivity; exact H21).
assert (E8 : ew Ev 8 = getr (e_regs X) (Z_to_bv 5 2)).
{ rewrite HEv, (exx_E_reg regs (e_regs X) _ 8%bv 8) by reflexivity. rewrite R8. unfold w64, exv_sp, spZ.
  rewrite Z_to_bv_bv_unsigned. all: try (f_equal; apply bv_eq; vm_compute; reflexivity). }
assert (E3 : ew Ev 3 = getr (e_regs X) (Z_to_bv 5 3)).
{ rewrite HEv, (exx_E_reg regs (e_regs X) _ 3%bv 3) by reflexivity. rewrite R3, <- Hgp.
  all: try (f_equal; apply bv_eq; vm_compute; reflexivity). }
assert (E4 : ew Ev 4 = getr (e_regs X) (Z_to_bv 5 4)).
{ rewrite HEv, (exx_E_reg regs (e_regs X) _ 4%bv 4) by reflexivity. rewrite R4, <- Htp.
  all: try (f_equal; apply bv_eq; vm_compute; reflexivity). }
assert (ES : forall j, (j < 13)%nat -> ew Ev (33 + j) = getr (e_regs X) (Z_to_bv 5 (snd (nth j exv_saved (0, 0))))).
{ intros j Hj. rewrite HEv. apply exx_E_saved. exact Hj. }
(* the run: the cut to `ret`, under the inline release *)
assert (FFLX2 : forall ly S Hp (W : world rsegs) mem md cid pos, ARx ly S Hp W mem md -> In (cid, pos) (frames S) ->
  aowned B ly S (flag_addr ly cid pos) /\ (app_addr (flag_addr ly cid pos) /\ ~ in_img rsegs (flag_addr ly cid pos))).
{ intros ly0 S0 Hp0 W0 m0 md0 c0 p0 H1 H2. destruct (eh_fflx B ARx SK HYP ly0 S0 Hp0 W0 m0 md0 c0 p0 H1 H2) as (_ & Ho & Hi & _).
  exact (conj Ho Hi). }
pose (FLAG := aj_flag_store_x (fx := fx) (rc := rc) (SK := SK) rsegs B PST ARx LAWS B_prog_segs_low (eh_asfx B ARx SK HYP) FFLX2
  (eh_sfx B ARx SK HYP) asym B_prog_wx (clookup B_prog_tbl) B_prog_val B_prog_sigma B_prog_listing B_prog_tpi B_prog_tw
  (@pa_fetch_ok _ B_prog_listing PI_prog_B) (@pa_cert _ B_prog_listing PI_prog_B) (@pa_B_ok _ B_prog_listing PI_prog_B)
  A_LIM A_LIM_text (@pl_lim _ PL_prog_B) (@pl_len _ PL_prog_B) (@pl_tpi_eq _ PL_prog_B) (@pl_tw_eq _ PL_prog_B)).
unfold cfg_at. change (w64 (exv_pc 0xa7c)) with (Z_to_bv 64 (BASE + EXX_PC)).
let rr := eval vm_compute in (sym_runN_pi_tok B_prog_tpi B_prog_tw 512 exx_Bx exx_Bspan exx_SH 400%N ss_exx) in
lazymatch rr with (?st', ?rs) =>
  assert (Hrun : sym_runN_pi_tok B_prog_tpi B_prog_tw 512 exx_Bx exx_Bspan exx_SH 400%N ss_exx = (st', rs))
    by (vm_compute; reflexivity)
end.
eapply (FLAG Wc 400%N Ev 512%nat exx_Bx exx_Bspan exx_SH ss_exx _ _ _ _ _ _ _ _ _ _ _ _ [] lyc Sc Hpc mdc k 1 pos _
  ltac:(unfold A_LIM; lia) HEI ltac:(lia) HS SHOK ltac:(vm_compute; reflexivity) Hrun I HJ).
- cbn [sh_obls]. apply Forall_nil.
- intros a Ha. rewrite HEv in Ha.
  destruct (exx_wr regs (e_regs X) (flag_addr lyc 1 pos) (frame_addr lyc 1 pos) a R18 R26 ltac:(lia) ltac:(lia) ltac:(lia) Ha)
    as [Hw | [Hw | Hw]].
  + left. right. right. right. exists 1, pos. split; [left; reflexivity|]. left. unfold in_zr. cbn [fst snd].
    rewrite exx_fb1. lia.
  + left. right. right. right. exists 1, pos. split; [left; reflexivity|]. right. unfold in_zr. cbn [fst snd].
    rewrite exx_fb1. change (128 / 8) with 16. lia.
  + right. exact Hw.
- intros ws msr Hl HSf. cbn [sh_j] in Hl. destruct ws; [|discriminate Hl]. cbn [extK] in HSf.
  pose proof (exx_region_nth _ _ msr 3 _ HSf eq_refl) as RG.
  assert (UFL : bv_unsigned (ew Ev 32) = flag_addr lyc 1 pos)
    by (rewrite HEv, exx_E_fl; unfold w64; apply unsigned_lit_small; lia).
  pose proof (exx_field _ _ 32 _ _ _ _ _ _ 0 1 (SLit 0) 0 RG UFL ltac:(left; reflexivity) eq_refl ltac:(cbn; lia) ltac:(cbn; lia))
    as V.
  specialize (V 0%nat ltac:(cbn; lia)). replace (flag_addr lyc 1 pos + 0 + Z.of_nat 0) with (flag_addr lyc 1 pos) in V by lia.
  exact V.
- clear HS HJ SHOK. paj_after_run_tok HS HJ SHOK.
  eapply (paj_ret_at (PL := PL_prog_B) (PI := PI_prog_B) Wc _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
  intros mat2.
  (* the bytes the run kept: everything but the frame's word, its shadow and the flag *)
  assert (KW : forall a, 0 <= a < 2 ^ 64 -> ~ (frame_addr lyc 1 pos <= a < frame_addr lyc 1 pos + 8) ->
     ~ (shadow_addr (frame_addr lyc 1 pos) <= a < shadow_addr (frame_addr lyc 1 pos) + 16) -> a <> flag_addr lyc 1 pos ->
     aview rsegs (w_H Wc) (ms_mem ms) a = aview rsegs (w_H Wc) memc a).
  { rewrite HEv in HFr.
    exact (exx_keep Wc regs (e_regs X) (flag_addr lyc 1 pos) memc (ms_mem ms) (frame_addr lyc 1 pos) HFr R18 R26
      ltac:(lia) ltac:(lia) ltac:(lia)). }
  assert (KALL : forall a, alloc_ceiling <= a < 2 ^ 64 -> aview rsegs (w_H Wc) (ms_mem ms) a = aview rsegs (w_H Wc) memc a).
  { intros a Ha. pose proof (Z.div_pos (frame_addr lyc 1 pos) 8 ltac:(lia) ltac:(lia)).
    apply KW; [lia | lia | unfold shadow_addr, SHADOW_OFF; lia | lia]. }
  (* memnorm: the run wrote only bytes the cut's memory defines (the frame, its shadow, the flag) *)
  assert (KMN : YAkMemnorm.memnorm rsegs memc -> YAkMemnorm.memnorm rsegs (ms_mem ms)).
  { apply (exx_memnorm_keep memc (ms_mem ms) (fun a => (frame_addr lyc 1 pos <= a < frame_addr lyc 1 pos + 8) \/
      (shadow_addr (frame_addr lyc 1 pos) <= a < shadow_addr (frame_addr lyc 1 pos) + 16) \/ a = flag_addr lyc 1 pos)).
    - intros a. apply exx_dec3.
    - intros x Hx. apply HF. rewrite HEv. intros Hw. apply Hx.
      exact (exx_wr regs (e_regs X) (flag_addr lyc 1 pos) (frame_addr lyc 1 pos) (bv_unsigned x) R18 R26
        ltac:(lia) ltac:(lia) ltac:(lia) Hw).
    - intros x [Hx | [Hx | Hx]].
      + destruct (Hfpres (bv_unsigned x) ltac:(lia)) as ((_ & b & Eb) & _). rewrite Z_to_bv_bv_unsigned in Eb.
        exists b. exact Eb.
      + destruct (Hshpres (bv_unsigned x - shadow_addr (frame_addr lyc 1 pos)) ltac:(lia)) as ((_ & b & Eb) & _).
        replace (shadow_addr (frame_addr lyc 1 pos) + (bv_unsigned x - shadow_addr (frame_addr lyc 1 pos))) with (bv_unsigned x)
          in Eb by lia.
        rewrite Z_to_bv_bv_unsigned in Eb. exists b. exact Eb.
      + destruct Hflpres as (_ & b & Eb). rewrite <- Hx, Z_to_bv_bv_unsigned in Eb. exists b. exact Eb. }
  (* the registers at `ret` *)
  exx_reg HS (1%bv : bv 5) Rra. exx_reg HS (10%bv : bv 5) Ra0.
  pose proof (ES 0%nat ltac:(lia)) as ES0. cbn [Nat.add nth exv_saved snd] in ES0.
  assert (RA : v_jalr (getr (ms_regs ms) 1) 0 = YK11.getr (e_regs X) 1).
  { rewrite Rra, ES0. replace (Z_to_bv 5 1) with (1%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity).
    unfold YK0s.ret_ok in Hra. exact Hra. }
  assert (AR : aregs_preserved (e_regs X) (ms_regs ms)).
  { intros rr Hrr. unfold acallee_saved in Hrr.
    assert (Hc : rr = 2 \/ rr = 3 \/ rr = 4 \/ rr = 8 \/ rr = 9 \/ rr = 18 \/ rr = 19 \/ rr = 20 \/ rr = 21 \/ rr = 22 \/
      rr = 23 \/ rr = 24 \/ rr = 25 \/ rr = 26 \/ rr = 27) by lia.
    destruct Hc as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]]]];
    lazymatch goal with |- getr _ (Z_to_bv 5 ?z) = _ =>
      let Q := fresh "Q" in exx_reg HS (Z_to_bv 5 z) Q; rewrite Q end;
    first [ exact E8 | exact E3 | exact E4
          | exact (ES 1%nat ltac:(lia)) | exact (ES 2%nat ltac:(lia)) | exact (ES 3%nat ltac:(lia))
          | exact (ES 4%nat ltac:(lia)) | exact (ES 5%nat ltac:(lia)) | exact (ES 6%nat ltac:(lia))
          | exact (ES 7%nat ltac:(lia)) | exact (ES 8%nat ltac:(lia)) | exact (ES 9%nat ltac:(lia))
          | exact (ES 10%nat ltac:(lia)) | exact (ES 11%nat ltac:(lia)) | exact (ES 12%nat ltac:(lia)) ]. }
  rewrite RA. unfold EXV_POST, fpostWFm, fpostWF, fQmn. cbv beta.
  exists fx, lyc, (stack_free_state 1 pos Sc), Hpc, (ms_regs ms), (ms_mem ms). eexists. exists k.
  split; [reflexivity|].
  split; [exact HFZ|]. split; [exact HFK|].
  split; [apply (ajournal_x_materialize (SK := SK) rsegs B PST ARx LAWS B_prog_segs_low); exact HJ|].
  split.
  { intros a Ha Hna. transitivity (aview rsegs (w_H Wc) memc a); [apply KALL; lia | exact (HWIN a Ha Hna)]. }
  split; [exact AR|].
  split; [| exact (fun h => KMN (HMN h))].
  split.
  { exact (exv_room_free (e_S X) Sc 1 pos HRM). }
  exists r. split; [rewrite Ra0; exact E21|].
  split.
  { destruct HRES as (p' & dep' & dl' & Hc & Hdl & Hm). exists p', dep', dl'.
    split; [|split; [exact Hdl | exact Hm]].
    unfold prhex_cur in Hc |- *. destruct Hc as (V1 & V2 & V3 & V4 & V5).
    assert (VQ : forall a (w : nat) v, val_mem rsegs (rdW Wc memc) a w v -> e_q X <= a -> a + Z.of_nat w <= e_q X + 40 ->
      val_mem rsegs (rdW Wc (ms_mem ms)) a w v).
    { intros a w v Hv H1 H2 kk Hk.
      rewrite (mbyte_of_aview rsegs (w_H Wc) (w_H Wc) memc (ms_mem ms) (a + Z.of_nat kk)); [exact (Hv kk Hk)|].
      apply KALL. lia. }
    refine (conj (VQ _ _ _ V1 _ _) (conj (VQ _ _ _ V2 _ _) (conj (VQ _ _ _ V3 _ _) (conj (VQ _ _ _ V4 _ _)
      (VQ _ _ _ V5 _ _))))); cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia. }
  split; [exact HHp|].
  split; [rewrite <- HAB; unfold ablocks; rewrite blocks_stack_free_state; reflexivity|].
  apply (exx_ledger lyc Sc Hpc Wc memc mdc (ms_mem ms) pos _ _ _ _ _ _ _ HAR Hin); [|exact HLED].
  intros a Ha N1 N2 N3. apply KW; [lia | exact N1 | exact N2 | exact N3].
Qed.

End c.

(* ---- the segment lemma: ExvB_Top.v's seg_exit, with EXV_HYP ---- *)
Lemma exvB_exit : forall {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive} B ARx SK,
  EXV_HYP B ARx SK -> forall n (fx : YK11.FPState), CUT_CX (fx := fx) B ARx SK n.
Proof. intros rc ci cp RL B ARx SK HYP n fx. exact (exx_cut (fx := fx) B ARx SK HYP n). Qed.
Print Assumptions exvB_exit.
