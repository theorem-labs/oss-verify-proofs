(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_headamp/lib/AU/HPgParseX.v at f2c1e970ff7d (image B's
   segEPI_ok / segEXIT_ok and their helpers, themselves made from proofs/reac-pw/fuzz_role/lib/A/RPgParseFV.v at
   afaa3cb55c1 fv_bytes .. fvw_beq_tk), restated for image A: image A's table pa_tbl and pcs, the names hpx_*, image
   A's EXIT (no alignment test; the key count in the frame cell spa + 40 and the refusal in s9, so res + 4 takes the
   frame cell and res + 8 takes s9), and the theorem names hp_segEPI_A / hp_segEXIT_A. *)
(* reac_headamp_prop_parse_result 0x845b4 of reac-pw/fuzz_headamp's ASan image A (fuzz_headamp.asan, pinned sha256
   f3e0669d2819724922df0556b11c2dcd22d1e16fe7e0fe1535ce784b34436c47; unstripped twin
   b5f352154c54a97c66fd92dfa228e8a854498f6cd313dba0107900546b043f9a, the same loaded bytes except .note.gnu.build-id): the walk's two exit
   segments of lib/A/HPgParseCut.v, hp_segEPI_A : segEPI_stmt B MT and hp_segEXIT_A : segEXIT_stmt B MT.
   proves function reac_headamp_prop_parse_result (segments EPI and EXIT of its walk; composed by lib/A/HPgParseJoin.v).
   Section hypotheses, of the list above HPgParseCut.v's segment statements: MTL : ameter_laws MT and
   errno_low : api_env rsegs B.

   EPI 0x84738 (EPI_at): `lui a0,0x45e03; addiw a0,a0,1550; sd a0,64(sp)` (the frame object's first word, at
   spa + 0x40), the close 0x84744 .. 0x84760 (eight `sb zero,k(s10)`, the hole's eight shadow bytes 0), `mv a0,s4`,
   `addi sp,s0,-256`, the 13 reloads `ld ra,248(sp)` .. `ld s11,152(sp)` (sp0 - 8 .. sp0 - 104), all walked by the
   engine (hpx_ss_epi: the frame object's word at sp = spa writable, the saved words as chunks at s0 = sp0, the hole
   at s10 writable; the run stops at the float load), then by hand `fld fs0,144(sp)` 0x847a0 (fs0 back to its entry
   bits), `addi sp,sp,256` 0x847a4 and `ret` 0x847a8: HPgParseGEx.pxg_epi_post gives hd_parse_post, the journal from
   HPgHole.hj_repat_raw (pattern PAT_ZERO) and hj_leave.
   EXIT 0x84890 (EXIT_at): `beqz s1,0x84738` (res = 0: EPI_at at once); else the three instrumented `sw` of n = s4 at
   res, keys = [spa + 40] (`ld a0,40(sp)`) at res + 4 and rf = s9 at res + 8 (each behind `srli / add s11 / lb / bnez`;
   their checks pass from range_addressable res 12, a shadow entry of the res atom; the slow arms 0x84e90, 0x84ea4,
   0x84eb4 are the token engine's `andi u,x,7; addi u,u,3; blt u,t,back`, and the error-path call behind each is not
   reached), `j 0x84738`: EPI_at with res = ans_res_bytes (Headamp.ha_result (cl, keys, rf)). *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YM05 YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK0o.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YN2e YO0f.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Lib Require Mem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Headamp.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Spec Require Import HeadBytes.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgBase HPgCSpec HPgHole HPgMem HPgParseBase HPgParseGEx.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgParseGKit.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A.Rt Require Import FMupoison.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import Img0 HPgImgA HPgParseCut.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* the key count is a value in Z: the frame cell holds its low 64 bits *)
Lemma hpx_val8_mod : forall m a v, val_mem rsegs m a 8 v -> val_mem rsegs m a 8 (v mod 2 ^ 64).
Proof.
intros m a v H k Hk. rewrite (H k Hk). do 2 f_equal.
unfold YO0f.le_byte. change (8 * Z.of_nat 8) with 64. rewrite Z.mod_mod by lia. reflexivity.
Qed.

Lemma hpx_lit_mod64 : forall v, Z_to_bv 64 (v mod 2 ^ 64) = Z_to_bv 64 v.
Proof.
intros v. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
apply Z.mod_mod. lia.
Qed.


(* ======================================= one instruction, by hand ======================================= *)
Definition hpx_bytes (n : nat) (v : Z) : list byte := map (fun k => Z_to_bv 8 (le_byte v n k)) (seq 0 n).

Lemma hpx_bytes_Z : forall n v, bytes_le_to_Z (hpx_bytes n v) = v mod 2 ^ (8 * Z.of_nat n).
Proof.
intros n v. pose proof (YN2e.bytes_le_to_Z_le_list_gen n v 0) as H.
cbn [Nat.add] in H. change (8 * Z.of_nat 0) with 0 in H. rewrite Z.shiftr_0_r in H. exact H.
Qed.

Lemma hpx_rdn8 : forall segs m a v, val_mem segs m a 8 v -> rdn segs m (Z_to_bv 64 a) 8 = Some (hpx_bytes 8 v).
Proof.
intros segs m a v H. apply (mbytes_at_rdn segs m a (hpx_bytes 8 v)).
intros j Hj. cbn [length hpx_bytes map seq] in Hj.
destruct j as [|[|[|[|[|[|[|[|j]]]]]]]]; try lia; cbn [nth_error hpx_bytes map seq]; apply H; lia.
Qed.

Lemma hpx_word8 : forall v, 0 <= v < 2 ^ 64 -> le_bytes_to_word (hpx_bytes 8 v) = Z_to_bv 64 v.
Proof.
intros v Hv. rewrite le_bytes_to_word_Z, hpx_bytes_Z. change (8 * Z.of_nat 8) with 64.
rewrite Z.mod_small by lia. reflexivity.
Qed.

Lemma hpx_addi_lit : forall z i, v_addi (Z_to_bv 64 z) i = Z_to_bv 64 (z + i).
Proof.
intros z i. unfold v_addi. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 64) with (2 ^ 64). apply Zplus_mod_idemp_l.
Qed.

Lemma hpx_fld : forall (F : bvmap 5 word) (fc : bv 32) regs mem rom p q wz rd rs (imm : bv 12) base off v,
clookup pa_tbl p = Some wz -> is_ecall (Z_to_bv 32 wz) = false ->
decode_any (Z_to_bv 32 wz) = Some (FLoad FMT_D rd rs imm, 4%Z) -> q = p + 4 ->
getr regs rs = Z_to_bv 64 base -> bv_signed imm = off ->
0 <= v < 2 ^ 64 -> val_mem rsegs mem (base + off) 8 v ->
RiscvSemantics.step rsegs (@mkst (mkFP F fc) regs (Z_to_bv 64 p) mem rom) =
MachineOk (@mkst (mkFP (bvmap_set rd (Z_to_bv 64 v) F) fc) regs (Z_to_bv 64 q) mem rom).
Proof.
intros F fc regs mem rom p q wz rd rs imm base off v Hc He Hd Hq Hrs Hoff Hv HM.
rewrite (fp_step_fld (mkFP F fc) rsegs regs (Z_to_bv 64 p) mem rom (Z_to_bv 32 wz) rd rs imm
  (v_addi (getr regs rs) (bv_signed imm)) (hpx_bytes 8 v) (pa_tbl_ok p wz Hc) He Hd eq_refl).
- cbn [fp_regs fp_csr]. rewrite Hq, hpx_addi_lit, hpx_word8 by lia. rewrite bv_extract_0_64. reflexivity.
- rewrite Hrs, Hoff, hpx_addi_lit. apply hpx_rdn8. exact HM.
Qed.

Lemma hpx_addi : forall (F : bvmap 5 word) (fc : bv 32) regs mem rom p q wz rd rs (imm : bv 12) off (v : word),
clookup pa_tbl p = Some wz -> is_ecall (Z_to_bv 32 wz) = false ->
decode_any (Z_to_bv 32 wz) = Some (OpImm ALU_ADD rd rs imm, 4%Z) ->
bv_eqb rd 0 = false -> q = p + 4 -> bv_signed imm = off ->
v = v_addi (getr regs rs) off ->
RiscvSemantics.step rsegs (@mkst (mkFP F fc) regs (Z_to_bv 64 p) mem rom) =
MachineOk (@mkst (mkFP F fc) (regupd regs rd v) (Z_to_bv 64 q) mem rom).
Proof.
intros F fc regs mem rom p q wz rd rs imm off v Hc He Hd Hrd Hq Hoff Hv.
rewrite (step_addi rsegs regs (Z_to_bv 64 p) mem rom (Z_to_bv 32 wz) rd rs imm (pa_tbl_ok p wz Hc) He Hd).
rewrite Hrd, Hq, hpx_addi_lit, Hoff, <- Hv. reflexivity.
Qed.

Lemma hpx_ret : forall (F : bvmap 5 word) (fc : bv 32) regs mem rom p wz rs1 (imm : bv 12) (t : word),
clookup pa_tbl p = Some wz -> is_ecall (Z_to_bv 32 wz) = false ->
decode_any (Z_to_bv 32 wz) = Some (Jalr 0 rs1 imm, 4%Z) ->
bv_signed imm = 0 -> getr regs rs1 = t -> YK0s.ret_ok t ->
RiscvSemantics.step rsegs (@mkst (mkFP F fc) regs (Z_to_bv 64 p) mem rom) =
MachineOk (@mkst (mkFP F fc) regs t mem rom).
Proof.
intros F fc regs mem rom p wz rs1 imm t Hc He Hd Himm Hr Hok.
rewrite (step_jalr_x0 rsegs regs (Z_to_bv 64 p) mem rom (Z_to_bv 32 wz) rs1 imm t (pa_tbl_ok p wz Hc) He Hd Hr).
rewrite Himm. unfold YK0s.ret_ok in Hok. rewrite Hok. reflexivity.
Qed.

Lemma hpx_getr_upd : forall regs (r r' : bv 5) v, bv_eqb r' r = false -> getr (regupd regs r v) r' = getr regs r'.
Proof.
intros regs r r' v H. unfold getr, regupd. destruct (bv_eqb r' 0); [reflexivity|].
unfold reg_get. rewrite bvmap_get_set_other; [reflexivity|].
intros E. unfold bv_eqb in H. apply Z.eqb_neq in H. apply H. rewrite E. reflexivity.
Qed.

Lemma hpx_getr_set : forall regs (r r' : bv 5) v, bv_eqb r' r = true -> bv_eqb r' 0 = false ->
getr (regupd regs r v) r' = v.
Proof.
intros regs r r' v H H0. unfold bv_eqb in H. apply Z.eqb_eq in H. apply bv_eq in H. subst r'.
unfold getr, regupd. rewrite H0. unfold reg_get. rewrite bvmap_get_set_same. reflexivity.
Qed.

Ltac hpx_dec := first [ (vm_compute; reflexivity) | vm_refl_bv ].

Lemma hpx_u64 : forall w : word, 0 <= bv_unsigned w < 2 ^ 64.
Proof. intros w. pose proof (bv_unsigned_in_range 64 w) as H. unfold bv_modulus in H. cbn [Z.of_N] in H. exact H. Qed.

(* ======================================= the engine's state at EPI ======================================= *)
Definition hpx_ss_epi : sstate := mkSS PC_EPI sr_atoms [pxg_r_fo; pxg_r_sv; pxg_r_h] None (mkFacts [] [] []).

Lemma hpx_region_val : forall (E : env) m r off (n : N) e v,
region_ok rsegs E m r -> In (YP09.mkChunk off (CVal n e)) (YP09.r_chunks r) ->
sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ (8 * Z.of_N n) -> Z.of_N n <= 8 ->
val_mem rsegs m (base_val E (YP09.r_base r) + off) (N.to_nat n) v.
Proof.
intros E m r off n e v Hr Hin He Hv Hn.
exact (val_of_chunk_ok rsegs E m _ off n e v (region_ok_chunk rsegs E m r _ Hr Hin) He Hv Hn).
Qed.

Lemma hpx_ew_extra : forall regs L i, ew (Ereg regs L) (32 + i) = nth i L (Z_to_bv 64 0).
Proof. intros regs L i. apply ew_Ereg_extra. Qed.

Lemma hpx_beq_tk : forall (F : bvmap 5 word) (fc : bv 32) regs mem rom p q wz rs1 rs2 (imm : bv 13),
clookup pa_tbl p = Some wz -> is_ecall (Z_to_bv 32 wz) = false ->
decode_any (Z_to_bv 32 wz) = Some (Branch BC_EQ rs1 rs2 imm, 4%Z) ->
getr regs rs1 = getr regs rs2 -> q = p + bv_signed imm ->
RiscvSemantics.step rsegs (@mkst (mkFP F fc) regs (Z_to_bv 64 p) mem rom) =
MachineOk (@mkst (mkFP F fc) regs (Z_to_bv 64 q) mem rom).
Proof.
intros F fc regs mem rom p q wz rs1 rs2 imm Hc He Hd Hr Hq.
rewrite (step_branch_tk_gen rsegs regs (Z_to_bv 64 p) mem rom (Z_to_bv 32 wz) BC_EQ rs1 rs2 imm
  (pa_tbl_ok p wz Hc) He Hd).
- unfold btgt. rewrite hpx_addi_lit, Hq. reflexivity.
- change (branch_taken BC_EQ (getr regs rs1) (getr regs rs2)) with (bv_eqb (getr regs rs1) (getr regs rs2)).
  rewrite Hr. apply bv_eqb_refl.
Qed.

(* ======================================= the engine's state at EXIT (res <> 0) ======================================= *)
(* the key count at spa + 40 (env slot 32), res's twelve bytes at s1 writable; the res atom in [4096, 2^47 - 12], 4-aligned, and
   s11 = SHADOW_OFF; the shadow entry of res's twelve bytes for the three instrumented `sw` *)
Definition hpx_r_tmp : YP09.region := YP09.mkRegion (Some 2%nat) 40 48 0 0 [YP09.mkChunk 40 (CVal 8 (SOff 32 0))].
Definition hpx_r_res : YP09.region := YP09.mkRegion (Some 9%nat) 0 12 0 12 [].
Definition hpx_ss_exit : sstate :=
mkSS PC_EXIT sr_atoms [hpx_r_tmp; hpx_r_res] None
  (mkFacts [(9%nat, mkAF 4096 (2 ^ 47 - 12) 2); (27%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] []).
Definition hpx_Bx : sv := SOff 27 0.
Definition hpx_Bspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
Definition hpx_SH : list shent := [mkSHE 9 0 12].

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis errno_low : api_env rsegs B.
Local Notation pctx := (@hp_ctx rsegs).
Implicit Types (x : pctx).

(* the entry state of EPI's run, at the cut's float state *)
Lemma hpx_epi_entry : forall x (F : bvmap 5 word) (fc : bv 32) cl rb regs mem md,
call_ok B x -> hp_core B x PAT_KEY cl rb regs mem md ->
st_ok (fx := mkFP F fc) rsegs (Ereg regs (pxg_saved x)) hpx_ss_epi
  (restrict (w_H (hx_W x)) (@mkst (mkFP F fc) regs (Z_to_bv 64 PC_EPI) mem (seg_rom rsegs))).
Proof.
intros x F fc cl rb regs mem md Hc HC.
pose proof (pxg_frame B _ _ _ _ _ _ _ x Hc) as (F32 & F1 & Fw & Fsp & F16 & Fceil & Flo & Fhi & F47 & F5 & F6 & _).
pose proof HC as (_ & _ & _ & HSV & _ & _ & _ & R2 & R8 & _ & _ & _ & _ & _ & R26 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HT : T_parse_STK = 0x120 + 3 * 4096) by reflexivity.
set (E := Ereg regs (pxg_saved x)).
assert (U2 : bv_unsigned (ew E 2) = hx_spa x).
{ subst E. rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl), R2. apply unsigned_lit_small. lia. }
assert (U8 : bv_unsigned (ew E 8) = hx_sp x).
{ subst E. rewrite (ew_Ereg_nat regs _ 8 8%bv eq_refl), R8. apply unsigned_lit_small. lia. }
assert (U26 : bv_unsigned (ew E 26) = hx_shf x).
{ subst E. rewrite (ew_Ereg_nat regs _ 26 26%bv eq_refl), R26. apply unsigned_lit_small.
  pose proof (pxg_hole_band B _ _ _ _ _ _ _ x (hx_shf x) Hc ltac:(unfold hp_hole; lia)) as (_ & _ & _ & H64). exact H64. }
pose proof (pxg_hole_band B _ _ _ _ _ _ _ x (hx_shf x) Hc ltac:(unfold hp_hole; lia)) as (HB1 & HB2 & HB3 & _).
pose proof (pxg_hole_band B _ _ _ _ _ _ _ x (hx_shf x + 7) Hc ltac:(unfold hp_hole; lia)) as (HB1' & HB2' & _).
rewrite restrict_mkst_fx. unfold hpx_ss_epi.
apply (entry_st_ok_full (fx := mkFP F fc) rsegs); change (Ereg regs (pxg_saved x)) with E.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- repeat apply Forall_cons; try apply Forall_nil.
  + unfold pxg_r_fo. apply (hm_rw_region rsegs E (w_H (hx_W x)) mem 2 (hx_spa x)); [exact U2 | lia | lia | |constructor].
    intros o Ho. apply (pxg_present B x PAT_KEY cl rb regs mem md HC). unfold hx_spa in *. lia.
  + unfold pxg_r_sv. apply (hm_ro_region rsegs E (w_H (hx_W x)) mem 8 (hx_sp x)); [exact U8 | lia | lia |].
    apply (pxg_sv_chunks_ok x mem E HSV). intros i Hi. subst E. apply hpx_ew_extra.
  + unfold pxg_r_h. apply (hm_rw_region rsegs E (w_H (hx_W x)) mem 26 (hx_shf x)); [exact U26 | lia | lia | |constructor].
    intros o Ho. exact (pxg_hole_present B pa_segs_low _ _ _ _ _ _ _ x PAT_KEY cl rb regs mem md Hc HC eq_refl o Ho).
- apply pairwise_disjoint_of_extents. unfold extent_of_region, pxg_r_fo, pxg_r_sv, pxg_r_h.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U2, U8, U26.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold hx_spa, hx_fr, hd_fr in *.
  repeat split; lia.
- repeat split.
Qed.

(* the hole's eight bytes read 0 when the region at s10 holds the eight `sb zero` chunks *)
Lemma hpx_hpat0 : forall x E (m : word -> option byte) r,
region_ok rsegs E (mrestrict (w_H (hx_W x)) m) r -> YP09.r_base r = Some 26%nat ->
bv_unsigned (ew E 26) = hx_shf x ->
(forall i, 0 <= i < 8 -> In (YP09.mkChunk i (CVal 1 (SLit 0))) (YP09.r_chunks r)) ->
hpat rsegs (hx_W x) m (hx_fr x) PAT_ZERO.
Proof.
intros x E m r Hr Hb H26 Hin i Hi. change (Z.of_nat (length PAT_ZERO)) with 8 in Hi.
pose proof (hpx_region_val E _ r i 1 (SLit 0) 0 Hr (Hin i Hi) ltac:(reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as V.
rewrite Hb in V. cbn [base_val] in V. rewrite H26 in V. unfold hx_shf in V.
assert (N0 : forall k, nth k PAT_ZERO 0 = 0)
  by (intros k; unfold PAT_ZERO; do 8 (destruct k as [|k]; [reflexivity|]); destruct k; reflexivity).
rewrite N0. apply (hm_val1_aview rsegs); [exact V | lia].
Qed.

(* the registers the epilogue's run leaves, as the engine holds them: ra, s0 .. s11 the saved words (env slots
   32 .. 44), gp, tp as at the cut, a0 = s4, sp = s0 - 256 *)
Definition hpx_leaf_sr : list (Z * sv) :=
[(1, SOff 32 0); (8, SOff 33 0); (9, SOff 34 0); (18, SOff 35 0); (19, SOff 36 0); (20, SOff 37 0);
 (21, SOff 38 0); (22, SOff 39 0); (23, SOff 40 0); (24, SOff 41 0); (25, SOff 42 0); (26, SOff 43 0);
 (27, SOff 44 0); (3, SOff 3 0); (4, SOff 4 0); (10, SOff 20 0); (2, SOff 8 (-256))].
Definition hpx_leaf_ok (sr : list sv) : bool :=
forallb (fun p => sv_eqb (sr_get sr (Z_to_bv 5 (fst p))) (snd p)) hpx_leaf_sr.

Lemma hpx_leaf_get : forall (F : bvmap 5 word) (fc : bv 32) E ss ms (H : word -> bool),
st_ok (fx := mkFP F fc) rsegs E ss (restrict H ms) -> hpx_leaf_ok (ss_regs ss) = true ->
forall r v, In (r, v) hpx_leaf_sr -> getr (ms_regs ms) (Z_to_bv 5 r) = sv_denot E v.
Proof.
intros F fc E ss ms H HS Hok r v Hin.
rewrite (st_ok_restrict_reg (fx := mkFP F fc) rsegs H E ss ms _ HS). apply sv_eqb_denot.
unfold hpx_leaf_ok in Hok. exact (proj1 (forallb_forall _ _) Hok (r, v) Hin).
Qed.

Ltac hpx_in := unfold hpx_leaf_sr; cbn [In]; repeat (first [left; reflexivity | right]).
(* a register the epilogue reloads from the saved word in env slot n = 32 + i *)
Ltac hpx_regsv G EX n i :=
  rewrite hpx_getr_upd by hpx_dec; rewrite (G _ (SOff n 0)) by hpx_in;
  rewrite pxg_sv_denot0; change n with (32 + i)%nat; rewrite EX; reflexivity.

Theorem hp_segEPI_A : segEPI_stmt B MT.
Proof.
unfold segEPI_stmt, EPI_ok. intros x Hc F fc regs mem md (HC & HFX & H20).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
pose proof (hpx_epi_entry x F fc _ _ regs mem md Hc HC) as HS.
pose proof (pxg_frame B _ _ _ _ _ _ _ x Hc) as (F32 & F1 & Fw & Fsp & F16 & Fceil & Flo & Fhi & F47 & F5 & F6 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HT : T_parse_STK = 0x120 + 3 * 4096) by reflexivity.
pose proof Hc as ((_ & Hra & _) & _).
pose proof HC as ((HJ & HOK & HPAT) & _ & _ & HSV & _ & _ & _ & R2 & R8 & R3 & R4 & _ & _ & _ & R26 & _).
pose proof (pxg_hole_band B _ _ _ _ _ _ _ x (hx_shf x) Hc ltac:(unfold hp_hole; lia)) as (_ & HB2 & _ & H64).
remember (Ereg regs (pxg_saved x)) as E eqn:HE.
assert (EA : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
  by (intros n r Hn; subst E; exact (ew_Ereg_nat regs _ n r Hn)).
assert (EX : forall i, ew E (32 + i) = nth i (pxg_saved x) (Z_to_bv 64 0)) by (intros i; subst E; apply hpx_ew_extra).
assert (U26 : bv_unsigned (ew E 26) = hx_shf x).
{ rewrite (EA 26%nat 26%bv eq_refl), R26. apply unsigned_lit_small. exact H64. }
assert (U2 : bv_unsigned (ew E 2) = hx_spa x).
{ rewrite (EA 2%nat 2%bv eq_refl), R2. apply unsigned_lit_small. unfold hx_spa in *. lia. }
assert (U8 : bv_unsigned (ew E 8) = hx_sp x).
{ rewrite (EA 8%nat 8%bv eq_refl), R8. apply unsigned_lit_small. lia. }
clear HE.
unfold cfg_at. change (w64 PC_EPI) with (Z_to_bv 64 PC_EPI).
aj_runH pa_tbl_ok HS HJ.
{ (* the run's writes: the frame object's word in the caller's stack window, the hole's bytes *)
  unfold hpx_ss_epi. cbn [ss_mem].
  eapply awr_okH_cons_gen; [reflexivity | exact U2 | |].
  { intros a Ha. left. left. cbn [YP09.r_wlo YP09.r_whi pxg_r_fo] in Ha. unfold hx_spa in *. lia. }
  apply awr_okH_cons_ro; [cbn; lia|].
  eapply awr_okH_cons_hole; [reflexivity | exact U26 | cbn; lia | cbn; lia |].
  apply awr_okH_nil. }
(* the run stopped at the float load 0x847a0 *)
pose proof (st_ok_mem_ok rsegs _ _ _ HS) as (_ & HRs & _). cbn [ss_mem ms_mem restrict] in HRs.
lazymatch type of HRs with Forall _ [?r1; ?r2; ?r3] =>
  pose proof (proj1 (Forall_forall _ _) HRs r2 ltac:(right; left; reflexivity)) as Hr2;
  pose proof (proj1 (Forall_forall _ _) HRs r3 ltac:(right; right; left; reflexivity)) as Hr3 end.
assert (HZ : hpat rsegs (hx_W x) (ms_mem ms) (hx_fr x) PAT_ZERO).
{ apply (hpx_hpat0 x E _ _ Hr3 eq_refl U26).
  intros i Hi. assert (i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7) as Hc8 by lia.
  cbn [YP09.r_chunks].
  repeat (destruct Hc8 as [-> | Hc8]; [cbn [In]; repeat (first [left; reflexivity | right]) |]).
  subst i. cbn [In]. repeat (first [left; reflexivity | right]). }
assert (HJZ : hjournal rsegs B (hx_STK x) (hx_sp0 x) (hx_FP x) (hx_ly x) (hx_S x) (hx_W0 x) (hx_mem0 x) (hx_md0 x)
  (hx_own x) (hx_lyc x) (hx_Sc x) (hx_W x) (ms_mem ms) (with_vm_backing (m_vm_lazy md) mat md) (hx_k x) (hx_fr x)
  PAT_ZERO).
{ eapply hj_repat_raw; [exact HJ | exact HOK | reflexivity | | exact HZ].
  unfold PAT_ZERO. repeat apply Forall_cons; try apply Forall_nil; lia. }
assert (HJ0 : ajournal rsegs B (hx_STK x) (hx_sp0 x) (hx_FP x) (hx_ly x) (hx_S x) (hx_W0 x) (hx_mem0 x) (hx_md0 x)
  (hx_own x) (hx_lyc x) (hx_Sc x) (hx_W x) (ms_mem ms) (with_vm_backing (m_vm_lazy md) mat md) (hx_k x)).
{ eapply hj_leave; [exact Hsegs | exact HJZ |]. unfold PAT_ZERO. repeat apply Forall_cons; try apply Forall_nil; reflexivity. }
(* fs0's entry bits at sp0 - 112 *)
set (b8 := Sem.reg_get (@fp_regs fx) (Z_to_bv 5 8)).
assert (V8 : val_mem rsegs (mrestrict (w_H (hx_W x)) (ms_mem ms)) (hx_sp x + -112) 8 (bv_unsigned b8)).
{ pose proof (hpx_region_val E _ _ (-112) 8 (SOff 45 0) (bv_unsigned b8) Hr2
    ltac:(cbn [YP09.r_chunks In]; repeat (first [left; reflexivity | right]))) as V.
  cbn [YP09.r_base base_val] in V. rewrite U8 in V. apply V.
  - rewrite pxg_sv_denot0. change 45%nat with (32 + 13)%nat. rewrite EX. symmetry. apply Z_to_bv_bv_unsigned.
  - apply bv_unsigned_in_range.
  - lia. }
(* the registers the run leaves *)
pose proof (hpx_leaf_get F fc E _ ms (w_H (hx_W x)) HS ltac:(vm_compute; reflexivity)) as G.
assert (G2 : getr (ms_regs ms) 2 = Z_to_bv 64 (hx_sp x - 256)).
{ replace (2%bv : bv 5) with (Z_to_bv 5 2) by (apply bv_eq; reflexivity).
  rewrite (G 2 (SOff 8 (-256))) by hpx_in. cbn [sv_denot]. rewrite U8. f_equal; try lia. }
assert (G1 : getr (ms_regs ms) 1 = getr (hx_regs x) 1).
{ replace (1%bv : bv 5) with (Z_to_bv 5 1) by (apply bv_eq; reflexivity).
  rewrite (G 1 (SOff 32 0)) by hpx_in. rewrite pxg_sv_denot0. change 32%nat with (32 + 0)%nat. rewrite EX.
  reflexivity. }
assert (G10 : getr (ms_regs ms) 10 = w64 (ans_rc (hx_ans x))).
{ replace (10%bv : bv 5) with (Z_to_bv 5 10) by (apply bv_eq; reflexivity).
  rewrite (G 10 (SOff 20 0)) by hpx_in. rewrite pxg_sv_denot0, (EA 20%nat 20%bv eq_refl). exact H20. }
(* fld fs0,144(sp); addi sp,sp,256; ret *)
pose proof (st_ok_restrict_mkst (fx := mkFP F fc) rsegs (w_H (hx_W x)) E _ ms HS eq_refl) as Hshape.
rewrite Hshape. cbn [ss_pc].
eapply (SRr_msteps rsegs Hwx).
{ rewrite restrict_mkst_fx.
  eapply mst_step;
  [ reflexivity
  | apply (hpx_fld F fc _ _ _ 0x847a0 0x847a4 0x09013407 8 2 144 (hx_sp x - 256) 144 (bv_unsigned b8));
    [ hpx_dec | hpx_dec | hpx_dec | reflexivity | exact G2 | hpx_dec | apply hpx_u64
    | replace (hx_sp x - 256 + 144) with (hx_sp x + -112) by lia; exact V8 ]
  | ].
  eapply mst_step;
  [ reflexivity
  | apply (hpx_addi (bvmap_set 8 (Z_to_bv 64 (bv_unsigned b8)) F) fc _ _ _ 0x847a4 0x847a8 0x10010113 2 2 256 256
      (Z_to_bv 64 (hx_sp x)));
    [ hpx_dec | hpx_dec | hpx_dec | hpx_dec | reflexivity | hpx_dec | rewrite G2, hpx_addi_lit; f_equal; try lia ]
  | ].
  eapply mst_step;
  [ reflexivity
  | apply (hpx_ret (bvmap_set 8 (Z_to_bv 64 (bv_unsigned b8)) F) fc _ _ _ 0x847a8 0x00008067 1 0
      (getr (hx_regs x) 1));
    [ hpx_dec | hpx_dec | hpx_dec | hpx_dec | rewrite hpx_getr_upd by hpx_dec; exact G1 | exact Hra ]
  | ].
  apply mst_refl. }
intros md2 Hsame Hcl.
rewrite (same_but_materialized_wvb _ md2 Hsame), unrestrict_mkst_mrestrict.
apply SRr_ret. unfold PPOST. rewrite Z_to_bv_bv_unsigned.
apply (pxg_epi_post B MT pa_segs_low _ _ _ _ _ _ _ errno_low MTL x PAT_KEY regs mem md
  (bvmap_set 8 b8 F) fc (regupd (ms_regs ms) 2 (Z_to_bv 64 (hx_sp x))) (ms_mem ms) _
  (fun a => in_wrange E (ss_mem hpx_ss_epi) a) Hc HC).
- eapply ajournal_materialize; try exact (AR_laws_ok rsegs B); try exact Hsegs. exact HJ0.
- eapply same_io_trans; apply pxg_same_io_wvb.
- intros a Ha Hn. unfold hx_view, aview, mbyte. rewrite (HFr (Z_to_bv 64 a)); [reflexivity|].
  rewrite unsigned_lit_small by lia. exact Hn.
- intros a (r & Hin & Ha). unfold hpx_ss_epi in Hin. cbn [ss_mem In] in Hin.
  destruct Hin as [<-|[<-|[<-|[]]]];
    cbn [pxg_r_fo pxg_r_sv pxg_r_h YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha.
  + rewrite U2 in Ha. left. unfold hx_spa in *. lia.
  + lia.
  + rewrite U26 in Ha. right. unfold hp_hole. lia.
- intros a Ha. unfold hp_hole, hx_shf in Ha.
  pose proof (HZ (a - shadow_addr (hx_fr x)) ltac:(change (Z.of_nat (length PAT_ZERO)) with 8; lia)) as Z1.
  replace (shadow_addr (hx_fr x) + (a - shadow_addr (hx_fr x))) with a in Z1 by lia.
  unfold hx_view. rewrite Z1. f_equal.
  unfold PAT_ZERO. destruct (Z.to_nat (a - shadow_addr (hx_fr x))) as [|[|[|[|[|[|[|[|k]]]]]]]];
    try reflexivity. destruct k; reflexivity.
- intros r Hr. unfold acallee_saved in Hr.
  assert (r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/
          r = 24 \/ r = 25 \/ r = 26 \/ r = 27) as Hr' by lia.
  destruct Hr' as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]]]].
  + rewrite hpx_getr_set by hpx_dec. unfold hx_sp, spZ. rewrite Z_to_bv_bv_unsigned.
    first [reflexivity | f_equal; apply bv_eq; reflexivity].
  + rewrite hpx_getr_upd by hpx_dec. rewrite (G 3 (SOff 3 0)) by hpx_in.
    rewrite pxg_sv_denot0, (EA 3%nat (Z_to_bv 5 3) eq_refl).
    replace (Z_to_bv 5 3) with (3%bv : bv 5) by (apply bv_eq; reflexivity). exact R3.
  + rewrite hpx_getr_upd by hpx_dec. rewrite (G 4 (SOff 4 0)) by hpx_in.
    rewrite pxg_sv_denot0, (EA 4%nat (Z_to_bv 5 4) eq_refl).
    replace (Z_to_bv 5 4) with (4%bv : bv 5) by (apply bv_eq; reflexivity). exact R4.
  + hpx_regsv G EX 33%nat 1%nat.
  + hpx_regsv G EX 34%nat 2%nat.
  + hpx_regsv G EX 35%nat 3%nat.
  + hpx_regsv G EX 36%nat 4%nat.
  + hpx_regsv G EX 37%nat 5%nat.
  + hpx_regsv G EX 38%nat 6%nat.
  + hpx_regsv G EX 39%nat 7%nat.
  + hpx_regsv G EX 40%nat 8%nat.
  + hpx_regsv G EX 41%nat 9%nat.
  + hpx_regsv G EX 42%nat 10%nat.
  + hpx_regsv G EX 43%nat 11%nat.
  + hpx_regsv G EX 44%nat 12%nat.
- rewrite hpx_getr_upd by hpx_dec. exact G1.
- exact (pxg_fxk_fs0 F fc 8 HFX eq_refl).
- rewrite hpx_getr_upd by hpx_dec. exact G10.
Qed.

(* a register the run keeps: its symbolic value is still its own atom n, below the run's new atoms *)
Lemma hpx_keep_reg : forall (F : bvmap 5 word) (fc : bv 32) E E' ss ms (H : word -> bool) regs (n : nat) (r : bv 5),
st_ok (fx := mkFP F fc) rsegs E' ss (restrict H ms) -> sv_eqb (sr_get (ss_regs ss) r) (SOff n 0) = true ->
ew E' n = ew E n -> ew E n = getr regs r -> getr (ms_regs ms) r = getr regs r.
Proof.
intros F fc E E' ss ms H regs n r HS Hb H1 H2.
rewrite (st_ok_restrict_reg (fx := mkFP F fc) rsegs H E' ss ms r HS), (sv_eqb_denot E' _ _ Hb), pxg_sv_denot0.
congruence.
Qed.

(* the entry state of EXIT's run (res <> 0), at the cut's float state *)
Lemma hpx_exit_entry : forall x (F : bvmap 5 word) (fc : bv 32) cl rb regs mem md rf,
call_ok B x -> hx_R x <> 0 -> hp_core B x PAT_KEY cl rb regs mem md -> length rb = 12%nat ->
val_mem rsegs (hx_rd x mem) (hx_spa x + 40) 8 rf -> 0 <= rf < 2 ^ 64 ->
st_ok (fx := mkFP F fc) rsegs (Ereg regs [w64 rf]) hpx_ss_exit
  (restrict (w_H (hx_W x)) (@mkst (mkFP F fc) regs (Z_to_bv 64 PC_EXIT) mem (seg_rom rsegs))).
Proof.
intros x F fc cl rb regs mem md rf Hc HR0 HC Hrb Hrf Hrf64.
pose proof (pxg_frame B _ _ _ _ _ _ _ x Hc) as (F32 & F1 & Fw & Fsp & F16 & Fceil & Flo & Fhi & F47 & F5 & F6 & _).
pose proof (pxg_res_facts B _ _ _ _ _ _ _ x Hc HR0) as (R4 & R4096 & R47 & _).
pose proof (pxg_res_apart B pa_segs_low _ _ _ _ _ _ _ x 0 Hc HR0 ltac:(lia)) as (A0 & _ & _).
pose proof (pxg_res_apart B pa_segs_low _ _ _ _ _ _ _ x 11 Hc HR0 ltac:(lia)) as (A11 & _ & _).
pose proof HC as (_ & _ & _ & _ & _ & HRb & _ & R2 & _ & _ & _ & R9 & _ & _ & _ & R27).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HT : T_parse_STK = 0x120 + 3 * 4096) by reflexivity.
set (E := Ereg regs [w64 rf]).
assert (U2 : bv_unsigned (ew E 2) = hx_spa x).
{ subst E. rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl), R2. apply unsigned_lit_small. unfold hx_spa in *. lia. }
assert (U9 : bv_unsigned (ew E 9) = hx_R x).
{ subst E. rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl), R9. apply unsigned_lit_small. lia. }
assert (U27 : bv_unsigned (ew E 27) = SHADOW_OFF).
{ subst E. rewrite (ew_Ereg_nat regs _ 27 27%bv eq_refl), R27. reflexivity. }
rewrite restrict_mkst_fx. unfold hpx_ss_exit.
apply (entry_st_ok_full (fx := mkFP F fc) rsegs); change (Ereg regs [w64 rf]) with E.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- repeat apply Forall_cons; try apply Forall_nil.
  + unfold hpx_r_tmp. apply (hm_ro_region rsegs E (w_H (hx_W x)) mem 2 (hx_spa x)); [exact U2 | lia | lia |].
    constructor; [|constructor].
    apply (chunk_ok_val rsegs E _ (hx_spa x) 40 8 (SOff 32 0) rf); [| cbn; lia | lia | exact Hrf].
    rewrite pxg_sv_denot0. subst E. change 32%nat with (32 + 0)%nat. rewrite hpx_ew_extra. reflexivity.
  + unfold hpx_r_res. apply (hm_rw_region rsegs E (w_H (hx_W x)) mem 9 (hx_R x)); [exact U9 | lia | lia | | constructor].
    intros o Ho.
    pose proof (pxg_res_apart B pa_segs_low _ _ _ _ _ _ _ x o Hc HR0 Ho) as (_ & _ & An).
    destruct (HRb HR0 (Z.to_nat o) ltac:(unfold hd_zbytes; rewrite length_map, Hrb; lia)) as (V & Vr).
    rewrite Z2Nat.id in V by lia.
    exact (pxg_aview_present _ _ (hx_R x + o) _ ltac:(lia) An (hm_val1_aview rsegs _ _ _ _ V Vr)).
- apply pairwise_disjoint_of_extents. unfold extent_of_region, hpx_r_tmp, hpx_r_res.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U2, U9.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold hx_spa in *.
  repeat split; lia.
- split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite U9, U27. change (2 ^ 2) with 4. rewrite Z.pow_0_r, Z.mod_1_r. unfold SHADOW_OFF in *. repeat split; lia.
Qed.

(* the shadow entry of res's twelve bytes at a cut *)
Lemma hpx_exit_sh : forall x cl rb regs mem md rf, call_ok B x -> hx_R x <> 0 ->
hp_core B x PAT_KEY cl rb regs mem md -> Z.of_nat (length cl) <= hx_cap x + 1 ->
sh_ok rsegs hpx_Bx hpx_SH (Ereg regs [w64 rf]) (mrestrict (w_H (hx_W x)) mem).
Proof.
intros x cl rb regs mem md rf Hc HR0 HC Hcl.
pose proof HC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & R9 & _ & _ & _ & R27).
pose proof (pxg_res_facts B _ _ _ _ _ _ _ x Hc HR0) as (R4 & R4096 & R47 & Hra).
pose proof (pxg_frame B _ _ _ _ _ _ _ x Hc) as (F32 & F1 & Fw & Fsp & F16 & _).
assert (HT : T_parse_STK = 0x120 + 3 * 4096) by reflexivity.
unfold sh_ok, hpx_SH, hpx_Bx. constructor; [|constructor].
apply (hk_shent_res B pa_segs_low x (w_H (hx_W x)) mem _ 9 0 12 Hc HR0).
- rewrite (ew_Ereg_nat regs _ 27 27%bv eq_refl), R27. reflexivity.
- rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl), R9. reflexivity.
- apply (hm_ra_kept rsegs (w_H (hx_W x)) (hx_memc x) (w_H (hx_W x)) mem SHADOW_OFF (hx_R x) 12 Hra).
  intros y Hy.
  pose proof (pxg_res_apart B pa_segs_low _ _ _ _ _ _ _ x (y - hx_R x) Hc HR0 ltac:(lia)) as (A1 & _ & _).
  replace (hx_R x + (y - hx_R x)) with y in A1 by lia.
  assert (D : 0 <= y / 8 < 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  apply (hk_kept_sh B pa_segs_low x PAT_KEY cl rb regs mem md _ errno_low Hc HC Hcl).
  + unfold shadow_of_addr, kHighShadowEnd, SHADOW_OFF in *. lia.
  + apply (hk_sh_not_hole B x y Hc). unfold hx_fr, hd_fr, hx_spa in *. lia.
- lia.
- lia.
Qed.

(* a register the EXIT run keeps (atom n below the run's new atoms 33, 34) *)
Ltac hpx_keep n r :=
  lazymatch goal with
  | HS : st_ok _ _ _ (restrict ?H ?ms), EA : forall (n0 : nat) (r0 : bv 5), _ -> ew ?E n0 = getr ?regs r0 |- _ =>
    eapply (hpx_keep_reg _ _ E _ _ ms H regs n r);
    [ exact HS | vm_compute; reflexivity | repeat rewrite ew_ewset_other by lia; reflexivity
    | apply EA; reflexivity ]
  end.

Theorem hp_segEXIT_A : segEXIT_stmt B MT.
Proof.
unfold segEXIT_stmt, EXIT_ok. intros x Hc HEPI cl keys rf F fc regs mem md (HC & HFX & HM & H20 & H25 & Hkey).
remember (keys mod 2 ^ 64) as kv eqn:Ekv0.
assert (Hkv : 0 <= kv < 2 ^ 64) by (rewrite Ekv0; apply Z.mod_pos_bound; lia).
assert (Ekv : w64 kv = w64 keys) by (rewrite Ekv0; apply hpx_lit_mod64).
assert (HV : val_mem rsegs (hx_rd x mem) (hx_spa x + 40) 8 kv) by (rewrite Ekv0; exact (hpx_val8_mod _ _ keys Hkey)).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
pose proof (pxg_ans_exit x cl keys rf HM) as Hans.
pose proof HM as (Hnull & (Hcl & Hk0 & Hrf5) & _).
assert (Hcl1 : Z.of_nat (length cl) <= hx_cap x + 1) by lia.
pose proof HC as ((HJ & HOK & HPAT) & _ & _ & _ & _ & _ & _ & R2 & R8 & R3 & R4 & R9 & R18 & R19 & R26 & R27).
destruct (Z.eq_dec (hx_R x) 0) as [R0|R0].
- (* res = 0: `beqz s1,0x84738` taken *)
  unfold cfg_at. change (w64 PC_EXIT) with (Z_to_bv 64 PC_EXIT).
  eapply (SRr_msteps rsegs Hwx).
  { rewrite restrict_mkst_fx.
    eapply mst_step;
    [ reflexivity
    | apply (hpx_beq_tk F fc _ _ _ 0x84890 0x84738 0xea0484e3 9 0 (Z_to_bv 13 (-344)));
      [ hpx_dec | hpx_dec | hpx_dec | rewrite R9, R0, getr_zero; reflexivity | hpx_dec ]
    | ].
    apply mst_refl. }
  intros md2 Hsame Hcl'.
  rewrite (same_but_materialized_wvb _ md2 Hsame), unrestrict_mkst_mrestrict.
  change (SRr rsegs (hx_W x) (cfg_at (fx := mkFP F fc) rsegs PC_EPI regs mem
    (with_vm_backing (m_vm_lazy md) (m_vm_materialized md2) md)) (PPOST B MT x)).
  apply HEPI. split; [|split; [exact HFX|]].
  + rewrite Hans. cbn [ans_cells ans_res_bytes Headamp.ha_result fst snd].
    apply (hk_core_wvb B pa_segs_low). apply (pxg_core_rb0 B x PAT_KEY cl (ha_res_bytes 0 0 0) _ regs mem md R0 HC).
  + rewrite Hans. cbn [ans_rc Headamp.ha_result fst snd]. exact H20.
- (* res <> 0: the three instrumented `sw`, then `j 0x84738` *)
  pose proof (pxg_res_facts B _ _ _ _ _ _ _ x Hc R0) as (R4' & R4096 & R47 & _).
  pose proof (hk_res B pa_segs_low x Hc R0) as (_ & _ & _ & HRW).
  pose proof (hpx_exit_entry x F fc cl _ regs mem md kv Hc R0 HC eq_refl HV Hkv) as HS.
  pose proof (hpx_exit_sh x cl _ regs mem md kv Hc R0 HC Hcl1) as SHOK.
  remember (Ereg regs [w64 kv]) as E eqn:HE.
  assert (EA : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
    by (intros n r Hn; subst E; exact (ew_Ereg_nat regs _ n r Hn)).
  assert (E32 : ew E 32 = w64 kv) by (subst E; reflexivity).
  assert (U9 : bv_unsigned (ew E 9) = hx_R x).
  { rewrite (EA 9%nat 9%bv eq_refl), R9. apply unsigned_lit_small. lia. }
  clear HE.
  unfold cfg_at. change (w64 PC_EXIT) with (Z_to_bv 64 PC_EXIT).
  aj_run_to_tokH pa_tbl_ok HS HJ SHOK hpx_Bspan PC_EPI.
  { unfold hpx_ss_exit. cbn [ss_mem].
    apply awr_okH_cons_ro; [cbn; lia|].
    eapply awr_okH_cons_gen; [reflexivity | exact U9 | |].
    { intros a Ha. left. cbn [YP09.r_wlo YP09.r_whi hpx_r_res] in Ha. exact (proj1 (HRW a ltac:(lia))). }
    apply awr_okH_nil. }
  (* the run stopped at EPI 0x84738 *)
  pose proof (st_ok_mem_ok rsegs _ _ _ HS) as (_ & HRs & _). cbn [ss_mem ms_mem restrict] in HRs.
  lazymatch type of HRs with Forall _ [?r1; ?r2] =>
    pose proof (proj1 (Forall_forall _ _) HRs r2 ltac:(right; left; reflexivity)) as Hr2 end.
  assert (HRES : hm_bytes rsegs (w_H (hx_W x)) (ms_mem ms) (hx_R x)
    (ha_res_bytes (Z.of_nat (length cl)) keys rf)).
  { pose proof (pxg_le4_chunk _ (w_H (hx_W x)) (ms_mem ms) _ 0 (SOff 20 0)
      (region_ok_chunk rsegs _ _ _ (YP09.mkChunk 0 (CVal 4 (SOff 20 0))) Hr2
        ltac:(cbn [YP09.r_chunks In]; repeat (first [left; reflexivity | right]))))
      as B0.
    pose proof (pxg_le4_chunk _ (w_H (hx_W x)) (ms_mem ms) _ 4 (SOff 32 0)
      (region_ok_chunk rsegs _ _ _ (YP09.mkChunk 4 (CVal 4 (SOff 32 0))) Hr2
        ltac:(cbn [YP09.r_chunks In]; repeat (first [left; reflexivity | right]))))
      as B4.
    pose proof (pxg_le4_chunk _ (w_H (hx_W x)) (ms_mem ms) _ 8 (SOff 25 0)
      (region_ok_chunk rsegs _ _ _ (YP09.mkChunk 8 (CVal 4 (SOff 25 0))) Hr2
        ltac:(cbn [YP09.r_chunks In]; repeat (first [left; reflexivity | right]))))
      as B8.
    cbn [YP09.r_base base_val] in B0, B4, B8. rewrite !pxg_sv_denot0 in B0, B4, B8.
    repeat rewrite ew_ewset_other in B0, B4, B8 by lia. rewrite U9 in B0, B4, B8.
    rewrite (EA 20%nat 20%bv eq_refl), H20 in B0. rewrite E32, Ekv in B4. rewrite (EA 25%nat 25%bv eq_refl), H25 in B8.
    unfold ha_res_bytes.
    apply (proj2 (hm_bytes_app rsegs _ _ _ _ _)). split; [rewrite Z.add_0_r in B0; exact B0|].
    rewrite Mem.length_le4. change (Z.of_nat 4) with 4.
    apply (proj2 (hm_bytes_app rsegs _ _ _ _ _)). split; [exact B4|].
    rewrite Mem.length_le4. change (Z.of_nat 4) with 4.
    replace (hx_R x + 4 + 4) with (hx_R x + 8) by lia. exact B8. }
  pose proof (st_ok_restrict_mkst (fx := mkFP F fc) rsegs (w_H (hx_W x)) _ _ ms HS eq_refl) as Hshape.
  rewrite Hshape. cbn [ss_pc sh_ss].
  change (SRr rsegs (hx_W x) (cfg_at (fx := mkFP F fc) rsegs PC_EPI (ms_regs ms) (ms_mem ms)
    (with_vm_backing (m_vm_lazy md) mat md)) (PPOST B MT x)).
  apply HEPI. split; [|split; [exact HFX|]].
  + rewrite Hans. cbn [ans_cells ans_res_bytes ans_n ans_keys ans_rf Headamp.ha_result fst snd].
    apply (pxg_core_step B pa_segs_low _ _ _ _ _ _ _ errno_low x PAT_KEY cl (ha_res_bytes 0 0 0) _ regs mem md
      (ms_regs ms) (ms_mem ms) _ (fun a => in_wrange E (ss_mem hpx_ss_exit) a) Hc Hcl HC).
    * eapply hj_repat_raw; [exact HJ | exact HOK | reflexivity | apply pxg_PAT_KEY_ok |].
      intros i Hi. rewrite <- (HPAT i Hi).
      pose proof (pxg_hole_band B _ _ _ _ _ _ _ x (hx_shf x + i) Hc ltac:(unfold hp_hole; cbn in Hi; lia))
        as (_ & _ & _ & H64).
      apply (pxg_frame_view x E _ mem (ms_mem ms) HFr); [exact H64|].
      intros (r & Hin & Ha). unfold hpx_ss_exit in Hin. cbn [ss_mem In] in Hin.
      destruct Hin as [<-|[<-|[]]]; cbn [hpx_r_tmp hpx_r_res YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
        [lia|]. rewrite U9 in Ha.
      pose proof (pxg_res_apart B pa_segs_low _ _ _ _ _ _ _ x (shadow_addr (hx_fr x) + i - hx_R x) Hc R0 ltac:(lia))
        as (_ & A2 & _).
      apply A2. unfold hp_hole, hx_shf. cbn in Hi. lia.
    * eapply same_io_trans; [apply same_io_refl | apply pxg_same_io_wvb].
    * exact (pxg_frame_view x E _ mem (ms_mem ms) HFr).
    * intros a (r & Hin & Ha). unfold hpx_ss_exit in Hin. cbn [ss_mem In] in Hin.
      destruct Hin as [<-|[<-|[]]]; cbn [hpx_r_tmp hpx_r_res YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
        [lia|]. rewrite U9 in Ha. right. right. split; [exact R0 | lia].
    * intros _. exact HRES.
    * hpx_keep 2%nat (2%bv : bv 5).
    * hpx_keep 8%nat (8%bv : bv 5).
    * hpx_keep 3%nat (3%bv : bv 5).
    * hpx_keep 4%nat (4%bv : bv 5).
    * hpx_keep 9%nat (9%bv : bv 5).
    * hpx_keep 18%nat (18%bv : bv 5).
    * hpx_keep 19%nat (19%bv : bv 5).
    * hpx_keep 26%nat (26%bv : bv 5).
    * hpx_keep 27%nat (27%bv : bv 5).
  + rewrite Hans. cbn [ans_rc Headamp.ha_result fst snd]. rewrite <- H20.
    hpx_keep 20%nat (20%bv : bv 5).
Qed.

End b.

Print Assumptions hp_segEPI_A.
Print Assumptions hp_segEXIT_A.
