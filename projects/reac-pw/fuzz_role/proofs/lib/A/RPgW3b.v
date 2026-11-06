(* reac-pw/fuzz_role image A (fuzz_role.asan, pinned sha256
   614cffc0864cc31d9d1ced61322c4efd567b64bc89fe09a227a05b5126e0debb; every address measured on the unstripped twin
   6da77bafc5c050954dd89149e1e55a24064c2211e3cbd351822d1c0a20900ad6, same loaded bytes): the two object-header
   pieces of the build (M01) of LLVMFuzzerTestOneInput 0x7ff88. Proves no function (kind: segment lemma). The
   preheader that follows them (PH 0x8051c -> N / P) is RPgW3bPre.v.

   THE TWO PIECES.
   - The Object header, BO 0x80364 -> PH 0x8051c (pod.h:392-395, shape <> 7): three pod_put32 calls
     (POD_OBJECT = 15; POD_OBJECT_PROPINFO 0x40001 when shape = 6 else POD_OBJECT_PROPS 0x40002; POD_PARAM_PROPS 2)
     at pp + 4, pp + 8, pp + 12, each with its two store checks (first and last byte of the 4) and the two 8-byte
     checks of pp->len, then is_props := (shape <> 6) at pp + 0x4008 with its 4-byte store check. len is 4 at BO,
     so every capacity test (`bltu len - 0x3ffd, -0x4001`) is decided on literals and falls through.
   - The Struct header, B7 0x802f4 -> PH 0x8051c (pod.h:389-391, shape = 7): one pod_put32 of POD_STRUCT = 14 at
     pp + 4 with its two store checks and the two checks of pp->len; is_props stays 0.

   HOW. Each piece rebuilds a symbolic state from its start cut (the registers as their own atoms, the R-relative
   cells and the two pp ranges as regions) and runs the kit's token engine (lib/Reusable/YCbn.v through
   YCbq.aj_run_to_tok). The shadow base is s7 = x23 itself (its atom has the exact range [SHADOW_OFF, SHADOW_OFF]),
   and two shadow entries (pp's 19744 bytes on x27, &pp->len's 16 bytes on x21) cover every check of the header:
   the engine reads each shadow byte as the literal 0, so no check leaves an obligation and no slow block is run.
   The stores into pp are allowed by the journal through RPgBase.rl_fresh_awr (pp is not live at the harness
   entry: RPgCSpec.rl_seg_pre's last conjunct). The values the Object header writes depend on the shape; the run
   leaves them as expressions in the shape's atom, and the end splits the shape into its seven values. *)
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YG0q YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YI16 YI00 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Pod Require Import Cursor Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import Img0 RPgBase RPgCSpec RPgImgA RPgMem RPgSeg.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require RPgCfgChanges.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

(* ===================================== the engine's context ===================================== *)
Definition W3B_BO : Z := 0x80364.
Definition W3B_PH : Z := 0x8051c.
Definition W3B_N : Z := 0x805e8.
Definition W3B_P : Z := 0x81ed4.
(* the 161 instruction words 0x80364 .. 0x805e4 *)
Definition w3b_tbl : ctable := build_table rsegs W3B_BO 161 TEmpty.
Lemma w3b_tbl_ok : table_ok rsegs w3b_tbl.
Proof. apply build_table_ok0. unfold W3B_BO. lia. Qed.
(* the shadow base is x23 (s7) *)
Definition w3b_Bx : sv := SOff 23 0.
Definition w3b_Bspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
(* the shadow address of &pp->len as the code keeps it in R+0xb0 (0x8023c .. 0x80244) *)
Definition w3b_shx : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff 21 0) (SLit 3)) (SOff 23 0).
(* pp on x27 (19744 bytes) and &pp->len on x21 (len and is_props) *)
Definition w3b_SH : list shent := [mkSHE 27 0 19744; mkSHE 21 0 16].
Definition W3B_PPHI : Z := 0x7fffff800000 - 19744.
Definition w3b_atoms : list (nat * afact) :=
[(21%nat, mkAF (4096 + 0x4000) (W3B_PPHI + 0x4000) 0); (27%nat, mkAF 4096 W3B_PPHI 0);
 (23%nat, mkAF SHADOW_OFF SHADOW_OFF 0)].
Definition W3B_M3FFD : Z := 0xffffffffffffc003.   (* -0x3ffd mod 2^64 *)
Definition W3B_A1BO : Z := 0xffffffffffffc007.    (* 4 - 0x3ffd mod 2^64 *)

(* ---- BO: the registers (a0 = len = 4, a1 = len - 0x3ffd), the three cells the header reads, pp's header
   words (written only) and &pp->len with len = 4. The shape is the extra atom 32. ---- *)
Definition w3b_regs_bo : list sv := sr_set (sr_set sr_atoms (Z_to_bv 5 10) (SLit 4)) (Z_to_bv 5 11) (SLit W3B_A1BO).
Definition w3b_slot_bo : YP09.region :=
YP09.mkRegion (Some 9%nat) 0x98 0xf0 0 0
[YP09.mkChunk 0x98 (CVal 8 (SOff 32 0)); YP09.mkChunk 0xb0 (CVal 8 w3b_shx); YP09.mkChunk 0xe8 (CVal 8 (SLit W3B_M3FFD))].
Definition w3b_hdr_r : YP09.region := YP09.mkRegion (Some 27%nat) 4 16 4 16 [].
Definition w3b_len_r : YP09.region := YP09.mkRegion (Some 21%nat) 0 12 0 12 [YP09.mkChunk 0 (CVal 8 (SLit 4))].
Definition w3b_ss_bo : sstate :=
mkSS W3B_BO w3b_regs_bo [w3b_slot_bo; w3b_hdr_r; w3b_len_r] None (mkFacts w3b_atoms [] []).

(* ---- B7: the same entry with the shape 7. The header is one word at pp + 4 and len (no is_props). The table
   runs 0x802f4 .. 0x805e4 (189 words). ---- *)
Definition W3B_B7 : Z := 0x802f4.
Definition w3b_tbl7 : ctable := build_table rsegs W3B_B7 189 TEmpty.
Lemma w3b_tbl7_ok : table_ok rsegs w3b_tbl7.
Proof. apply build_table_ok0. unfold W3B_B7. lia. Qed.
Definition w3b_hdr7_r : YP09.region := YP09.mkRegion (Some 27%nat) 4 8 4 8 [].
Definition w3b_len7_r : YP09.region := YP09.mkRegion (Some 21%nat) 0 8 0 8 [YP09.mkChunk 0 (CVal 8 (SLit 4))].
Definition w3b_ss_b7 : sstate :=
mkSS W3B_B7 w3b_regs_bo [w3b_slot_bo; w3b_hdr7_r; w3b_len7_r] None (mkFacts w3b_atoms [] []).

(* ===================================== byte-list facts ===================================== *)
Lemma w3b_nth_overwrite : forall (l x : list byte) o j d, (o + length x <= length l)%nat ->
nth j (overwrite l o x) d = if ((o <=? j) && (j <? o + length x))%nat then nth (j - o)%nat x d else nth j l d.
Proof.
intros l x o j d Hl. unfold overwrite.
destruct (Nat.ltb_spec j o) as [Hj|Hj].
- rewrite app_nth1 by (rewrite length_firstn; lia). rewrite nth_firstn.
  replace (j <? o)%nat with true by (symmetry; apply Nat.ltb_lt; lia).
  replace (o <=? j)%nat with false by (symmetry; apply Nat.leb_gt; lia). reflexivity.
- rewrite app_nth2 by (rewrite length_firstn; lia). rewrite length_firstn.
  replace (Nat.min o (length l)) with o by lia.
  replace (o <=? j)%nat with true by (symmetry; apply Nat.leb_le; lia). cbn [andb].
  destruct (Nat.ltb_spec j (o + length x)) as [Hk|Hk].
  + rewrite app_nth1 by lia. reflexivity.
  + rewrite app_nth2 by lia. rewrite nth_skipn. f_equal. lia.
Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Variable B : asyms.

(* a register the final symbolic state still holds as its own atom keeps its value *)
Lemma w3b_reg_kept : forall E ss ms regs0 extra (H : word -> bool) (r : bv 5),
st_ok rsegs E ss (restrict H ms) -> (forall n, (n < 32)%nat -> ew E n = ew (Ereg regs0 extra) n) ->
sr_get (ss_regs ss) r = SOff (Z.to_nat (bv_unsigned r)) 0 -> getr (ms_regs ms) r = getr regs0 r.
Proof.
intros E ss ms regs0 extra H r HS HA Hq.
rewrite (st_ok_restrict_reg rsegs H E ss ms r HS), Hq. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
pose proof (u5_range r) as Hr. rewrite HA by lia. apply ew_Ereg_reg.
Qed.

(* one byte a run stored, as the walk reads it back: a CVal 1 chunk of a final region at base + off *)
Lemma w3b_chunk1 : forall E (H : word -> bool) ms base off e (b : byte),
YP09.chunk_ok rsegs E (ms_mem (restrict H ms)) base (YP09.mkChunk off (CVal 1 e)) ->
byte_of_word (sv_denot E e) 0 = b -> forall a, a = base + off -> aview rsegs H (ms_mem ms) a = Some (bv_unsigned b).
Proof.
intros E H ms base off e b C Hb a ->. destruct (C 0 ltac:(cbn; lia)) as (b' & H1 & H2).
cbn [YP09.cbyte YP09.c_val YP09.c_off] in H1, H2. injection H1 as <-. rewrite Z.add_0_r in H2.
unfold aview. change (mrestrict H (ms_mem ms)) with (ms_mem (restrict H ms)). rewrite H2, Hb. reflexivity.
Qed.

(* the registers the header's run leaves alone: all but a0 .. a4 *)
Definition W3B_KEPT_BO : list Z :=
[1; 2; 3; 4; 5; 6; 7; 8; 9; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31].

Ltac w3b_kept_regs HS HAE E ms regs extra W :=
let r := fresh "r" in let Hr := fresh "Hr" in
intros r Hr; cbv [W3B_KEPT_BO] in Hr;
repeat (destruct Hr as [<-|Hr];
  [eapply (w3b_reg_kept E _ ms regs extra (w_H W)); [exact HS | exact HAE | vm_compute; reflexivity] |]);
destruct Hr.

(* ===================================== BO -> PH: the Object header =====================================
   0x80364 .. 0x80518. Entry facts: a0 = len = 4, a1 = len - 0x3ffd, s1 = R, s5 = pp + 0x4000, s7 = SHADOW_OFF,
   s11 = pp; the cells R+0x98 (shape), R+0xb0 (the shadow address of &pp->len), R+0xe8 (-0x3ffd); len = 4 in pp.
   At 0x8051c: a0 .. a4 changed, the header bytes at pp + 4, len = 16, is_props = (shape <> 6), every other
   byte as before. *)
Lemma w3b_hdr_core : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world rsegs) memc mdc k
(regs : bvmap 5 word) (R pp sh : Z) (Q : world rsegs -> config -> Prop),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
In (pp, PP_SIZE) (ablocks B lyc Sc) -> ~ In (pp, PP_SIZE) (ablocks B ly S) ->
sp0 - STK <= R -> R + 0x100 <= sp0 ->
getr regs (Z_to_bv 5 9) = w64 R -> getr regs (Z_to_bv 5 10) = w64 4 ->
getr regs (Z_to_bv 5 11) = w64 (4 - 0x3ffd) -> getr regs (Z_to_bv 5 21) = w64 (pp + 0x4000) ->
getr regs (Z_to_bv 5 23) = w64 SHADOW_OFF -> getr regs (Z_to_bv 5 27) = w64 pp ->
0 <= sh <= 6 ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x98) 8 (sh mod 2 ^ 64) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0xb0) 8 (shadow_addr (pp + 0x4000) mod 2 ^ 64) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0xe8) 8 (-0x3ffd mod 2 ^ 64) ->
val_mem rsegs (mrestrict (w_H W) memc) (pp + 0x4000) 8 4 ->
(forall (regs2 : bvmap 5 word) mem2 md2,
 ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem2 md2 k ->
 same_io mdc md2 ->
 (forall r, In r W3B_KEPT_BO -> getr regs2 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
 (forall a, 0 <= a < 2 ^ 64 -> ~ (pp + 4 <= a < pp + 16) -> ~ (pp + 0x4000 <= a < pp + 0x400c) ->
  aview rsegs (w_H W) mem2 a = aview rsegs (w_H W) memc a) ->
 rm_bytes rsegs (w_H W) mem2 (pp + 4) (hdr_bytes sh) ->
 rm_bytes rsegs (w_H W) mem2 (pp + 0x4000) (le64 16) ->
 rm_bytes rsegs (w_H W) mem2 (pp + 0x4008) (le32 (Z.b2z (negb (sh =? 6)))) ->
 SRr rsegs W (cfg_at rsegs W3B_PH regs2 mem2 md2) Q) ->
SRr rsegs W (cfg_at rsegs W3B_BO regs memc mdc) Q.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R pp sh Q HJ Hin Hout HR0 HR1
  R9 R10 R11 R21 R23 R27 Hsh V98 Vb0 Ve8 Vlen KONT.
pose proof (AR_laws_ok rsegs B) as LAWS.
pose proof RPgCfgChanges.cfg_wx as Hwx. pose proof RPgCfgChanges.cfg_segs_low as Hsegs.
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (_ & HSTK0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & _ & _ & _ & _).
assert (Erq : req_size PP_SIZE = 19744) by reflexivity.
destruct (al_blocks _ _ LAWS _ _ _ _ _ pp PP_SIZE HAR Hin) as (_ & Hpp0 & Hppc & Happ & Hppr & _).
rewrite Erq in Hppc, Happ, Hppr.
remember (Ereg regs [Z_to_bv 64 sh]) as E eqn:HE.
assert (HAE : forall n, (n < 32)%nat -> ew E n = ew (Ereg regs [Z_to_bv 64 sh]) n) by (intros; subst E; reflexivity).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
  by (intros n r Hn; subst E; exact (ew_Ereg_nat regs _ n r Hn)).
assert (E32 : ew E 32 = Z_to_bv 64 sh) by (subst E; exact (ew_Ereg_extra regs _ 0)).
assert (U9 : bv_unsigned (ew E 9) = R) by (rewrite (EE 9%nat (Z_to_bv 5 9) eq_refl), R9; apply unsigned_lit_small; lia).
assert (U21 : bv_unsigned (ew E 21) = pp + 0x4000)
  by (rewrite (EE 21%nat (Z_to_bv 5 21) eq_refl), R21; apply unsigned_lit_small; lia).
assert (U23 : bv_unsigned (ew E 23) = SHADOW_OFF)
  by (rewrite (EE 23%nat (Z_to_bv 5 23) eq_refl), R23; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U27 : bv_unsigned (ew E 27) = pp) by (rewrite (EE 27%nat (Z_to_bv 5 27) eq_refl), R27; apply unsigned_lit_small; lia).
assert (E21 : ew E 21 = Z_to_bv 64 (pp + 0x4000)) by (rewrite <- U21; symmetry; apply Z_to_bv_bv_unsigned).
assert (E23 : ew E 23 = Z_to_bv 64 SHADOW_OFF) by (rewrite <- U23; symmetry; apply Z_to_bv_bv_unsigned).
(* the symbolic state at BO *)
assert (HS : st_ok rsegs E w3b_ss_bo (restrict (w_H W) (mkst regs (Z_to_bv 64 W3B_BO) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. rewrite HE. unfold w3b_ss_bo. apply (entry_st_ok_full rsegs).
  - unfold w3b_regs_bo. apply regs_ok_rereg; [apply regs_ok_rereg; [apply regs_ok_Ereg | reflexivity |] | reflexivity |].
    + rewrite R10. reflexivity.
    + rewrite R11. unfold w64. cbn [sv_denot]. apply Z_to_bv64_eq_mod. reflexivity.
  - vm_compute. reflexivity.
  - rewrite <- HE. repeat apply Forall_cons; try apply Forall_nil.
    + unfold region_ok, w3b_slot_bo. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      * apply (chunk_ok_val rsegs E _ R 0x98 8 (SOff 32 0) (sh mod 2 ^ 64)); [| | cbn; lia | exact V98].
        -- cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. symmetry. apply Z_to_bv64_mod.
        -- pose proof (Z.mod_pos_bound sh (2 ^ 64) ltac:(lia)). cbn. lia.
      * apply (chunk_ok_val rsegs E _ R 0xb0 8 w3b_shx (shadow_addr (pp + 0x4000) mod 2 ^ 64)); [| | cbn; lia | exact Vb0].
        -- unfold w3b_shx. rewrite denot_lit_U. apply Z_to_bv64_eq_mod.
           rewrite !U_SAlu. cbn [zalu_raw]. rewrite U_SLit, (U_atom E 21 (pp + 0x4000) E21) by lia.
           rewrite (U_atom E 23 SHADOW_OFF E23) by (unfold SHADOW_OFF; lia).
           change (Z.land (zcanon 3) 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
           unfold shadow_addr, zcanon, M64.
           assert (0 <= (pp + 0x4000) / 8 < 2 ^ 61) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
           rewrite (Z.mod_small ((pp + 0x4000) / 8)) by lia.
           rewrite (Z.mod_small ((pp + 0x4000) / 8 + SHADOW_OFF)) by (unfold SHADOW_OFF; lia).
           rewrite Z.mod_mod by lia. f_equal. lia.
        -- pose proof (Z.mod_pos_bound (shadow_addr (pp + 0x4000)) (2 ^ 64) ltac:(lia)). cbn. lia.
      * apply (chunk_ok_val rsegs E _ R 0xe8 8 (SLit W3B_M3FFD) (-0x3ffd mod 2 ^ 64));
        [reflexivity | split; [vm_compute; discriminate | vm_compute; reflexivity] | cbn; lia | exact Ve8].
    + unfold region_ok, w3b_hdr_r. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U27. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable rsegs). apply (proj1 (Hppr (pp + o) ltac:(lia))).
    + unfold region_ok, w3b_len_r. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U21. split; [lia|]. split; [lia|].
      split; [intros o Ho; apply (apresent_writable rsegs); apply (proj1 (Hppr (pp + 0x4000 + o) ltac:(lia)))|].
      constructor; [|constructor].
      apply (chunk_ok_val rsegs E _ (pp + 0x4000) 0 8 (SLit 4) 4);
        [reflexivity | split; [vm_compute; discriminate | vm_compute; reflexivity] | cbn; lia |].
      rewrite Z.add_0_r. exact Vlen.
  - rewrite <- HE. apply pairwise_disjoint_of_extents. unfold extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val w3b_slot_bo w3b_hdr_r w3b_len_r]. rewrite U9, U21, U27.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
  - rewrite <- HE. split; [|split; exact I]. cbn [f_atoms w3b_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U21, U27, U23. rewrite !Z.pow_0_r, !Z.mod_1_r. unfold W3B_PPHI, SHADOW_OFF. repeat split; lia. }
assert (SHOK : sh_ok rsegs w3b_Bx w3b_SH E (mrestrict (w_H W) memc)).
{ unfold sh_ok, w3b_SH. repeat apply Forall_cons; try apply Forall_nil;
  unfold shent_ok, app_apart, w3b_Bx; cbn [she_m she_lo she_hi];
  rewrite ?(U_atom E 23 SHADOW_OFF E23) by (unfold SHADOW_OFF; lia).
  - rewrite (U_atom E 27 pp) by (try (rewrite <- U27; symmetry; apply Z_to_bv_bv_unsigned); lia).
    split.
    + change (rd_of rsegs (mrestrict (w_H W) memc)) with (aview rsegs (w_H W) memc).
      apply (range_addressable_of_block rsegs B LAWS lyc Sc W memc mdc pp PP_SIZE); [exact HAR | exact Hin | lia | rewrite Erq; lia].
    + intros a Ha. unfold in_app, kLowShadowBeg, kHighMemBeg in Happ. unfold SHADOW_OFF. lia.
  - rewrite (U_atom E 21 (pp + 0x4000) E21) by lia.
    split.
    + change (rd_of rsegs (mrestrict (w_H W) memc)) with (aview rsegs (w_H W) memc).
      apply (range_addressable_of_block rsegs B LAWS lyc Sc W memc mdc pp PP_SIZE); [exact HAR | exact Hin | lia | rewrite Erq; lia].
    + intros a Ha. unfold in_app, kLowShadowBeg, kHighMemBeg in Happ. unfold SHADOW_OFF. lia. }
clear HE.
unfold cfg_at. change (w64 W3B_BO) with (Z_to_bv 64 W3B_BO).
aj_run_to_tok w3b_tbl_ok HS HJ SHOK w3b_Bspan W3B_PH.
{ (* the run writes pp's header words and &pp->len's 12 bytes: pp is a block of this segment's journal *)
  lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?sp ?fp ?b0 ?bc ?ly0 ?own0 =>
    let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk sp fp b0 bc ly0 own0) end.
  apply awr_ok_cons_ro; [cbn; lia|].
  eapply awr_ok_cons_gen; [reflexivity | exact U27 | | ].
  { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. replace a with (pp + (a - pp)) by lia.
    apply (rl_fresh_awr _ _ _ _ _ _ _ pp PP_SIZE); [exact Hin | exact Hout | rewrite Erq; lia]. }
  eapply awr_ok_cons_gen; [reflexivity | exact U21 | | apply awr_ok_nil].
  intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. replace a with (pp + (a - pp)) by lia.
  apply (rl_fresh_awr _ _ _ _ _ _ _ pp PP_SIZE); [exact Hin | exact Hout | rewrite Erq; lia]. }
(* ---- the state at 0x8051c ---- *)
pose proof (st_ok_mem_ok rsegs _ _ _ HS) as (_ & HOK & _). cbn [ss_mem] in HOK.
pose proof (Forall_inv (Forall_inv_tail HOK)) as (_ & _ & _ & Ch).
pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail HOK))) as (_ & _ & _ & Cl).
cbn [YP09.r_base YP09.r_chunks base_val] in Ch, Cl. rewrite U27 in Ch. rewrite U21 in Cl. clear HOK.
repeat rewrite Forall_cons_iff in Ch. repeat rewrite Forall_cons_iff in Cl.
destruct Cl as (Cisp & Clen & _).
destruct Ch as (C15 & C14 & C13 & C12 & C11 & C10 & C9 & C8 & C7 & C6 & C5 & C4 & _).
assert (Hs7 : sh = 0 \/ sh = 1 \/ sh = 2 \/ sh = 3 \/ sh = 4 \/ sh = 5 \/ sh = 6) by lia.
rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ ms HS eq_refl) at 1.
apply (KONT (ms_regs ms) (ms_mem ms)).
- exact HJ.
- apply RPgCfgChanges.same_io_wvb.
- w3b_kept_regs HS HAE E ms regs [Z_to_bv 64 sh] W.
- intros a Ha Ha1 Ha2. unfold aview, mbyte. rewrite (HFr (Z_to_bv 64 a)); [reflexivity|].
  rewrite unsigned_lit_small by lia. intros (rg & Hr & Hb).
  lazymatch type of Hr with In _ ?rs => let rs' := eval vm_compute in rs in change (In rg rs') in Hr end.
  repeat (destruct Hr as [<- | Hr];
    [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb; rewrite ?U27, ?U21 in Hb; lia | ]).
  destruct Hr.
- (* the twelve header bytes, one CVal 1 chunk each, at each of the seven shapes *)
  apply (proj2 (rm_bytes_aview rsegs (w_H W) (ms_mem ms) (pp + 4) (hdr_bytes sh))). intros i Hi.
  destruct Hs7 as [Hs|[Hs|[Hs|[Hs|[Hs|[Hs|Hs]]]]]]; rewrite Hs in E32, Hi |- *; cbn in Hi;
  (do 12 (destruct i as [|i];
    [ match goal with C : YP09.chunk_ok _ _ _ _ (YP09.mkChunk ?o (CVal 1 _)) |- _ =>
        eapply (w3b_chunk1 E (w_H W) ms pp o _ _ C);
        [ | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia];
        cbn [sv_denot]; rewrite ?E32; vm_compute; reflexivity end | ])); lia.
- (* len = 16 *)
  apply rm_bytes_of_val. rewrite <- (Z.add_0_r (pp + 16384)).
  exact (val_of_chunk_ok rsegs E _ (pp + 16384) 0 8 (SLit 16) 16 Clen eq_refl
    ltac:(split; [vm_compute; discriminate | vm_compute; reflexivity]) ltac:(cbn; lia)).
- (* is_props = (shape <> 6) *)
  apply rm_bytes_of_val. replace (pp + 16392) with (pp + 16384 + 8) by lia.
  apply (val_of_chunk_ok rsegs E _ (pp + 16384) 8 4 _ _ Cisp); [ | | cbn; lia].
  + destruct Hs7 as [Hs|[Hs|[Hs|[Hs|[Hs|[Hs|Hs]]]]]]; rewrite Hs in E32 |- *;
    cbn [sv_denot]; rewrite E32; vm_compute; reflexivity.
  + destruct (negb (sh =? 6)); cbn; lia.
Qed.

(* ===================================== B7 -> PH: the shape-7 header =====================================
   0x802f4 .. 0x80360 (pod.h:389-391): one pod_put32 of POD_STRUCT at pp + 4 with its two store checks and the
   two checks of pp->len, then `j` 0x8051c. Entry facts as at BO with the shape 7. At 0x8051c: a0 .. a2 changed,
   the four header bytes at pp + 4, len = 8, every other byte as before (is_props stays 0). *)
Lemma w3b_b7_core : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world rsegs) memc mdc k
(regs : bvmap 5 word) (R pp : Z) (Q : world rsegs -> config -> Prop),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
In (pp, PP_SIZE) (ablocks B lyc Sc) -> ~ In (pp, PP_SIZE) (ablocks B ly S) ->
sp0 - STK <= R -> R + 0x100 <= sp0 ->
getr regs (Z_to_bv 5 9) = w64 R -> getr regs (Z_to_bv 5 10) = w64 4 ->
getr regs (Z_to_bv 5 11) = w64 (4 - 0x3ffd) -> getr regs (Z_to_bv 5 21) = w64 (pp + 0x4000) ->
getr regs (Z_to_bv 5 23) = w64 SHADOW_OFF -> getr regs (Z_to_bv 5 27) = w64 pp ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x98) 8 (7 mod 2 ^ 64) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0xb0) 8 (shadow_addr (pp + 0x4000) mod 2 ^ 64) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0xe8) 8 (-0x3ffd mod 2 ^ 64) ->
val_mem rsegs (mrestrict (w_H W) memc) (pp + 0x4000) 8 4 ->
(forall (regs2 : bvmap 5 word) mem2 md2,
 ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem2 md2 k ->
 same_io mdc md2 ->
 (forall r, In r W3B_KEPT_BO -> getr regs2 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
 (forall a, 0 <= a < 2 ^ 64 -> ~ (pp + 4 <= a < pp + 8) -> ~ (pp + 0x4000 <= a < pp + 0x4008) ->
  aview rsegs (w_H W) mem2 a = aview rsegs (w_H W) memc a) ->
 rm_bytes rsegs (w_H W) mem2 (pp + 4) (hdr_bytes 7) ->
 rm_bytes rsegs (w_H W) mem2 (pp + 0x4000) (le64 8) ->
 SRr rsegs W (cfg_at rsegs W3B_PH regs2 mem2 md2) Q) ->
SRr rsegs W (cfg_at rsegs W3B_B7 regs memc mdc) Q.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R pp Q HJ Hin Hout HR0 HR1
  R9 R10 R11 R21 R23 R27 V98 Vb0 Ve8 Vlen KONT.
pose proof (AR_laws_ok rsegs B) as LAWS.
pose proof RPgCfgChanges.cfg_wx as Hwx. pose proof RPgCfgChanges.cfg_segs_low as Hsegs.
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (_ & HSTK0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & _ & _ & _ & _).
assert (Erq : req_size PP_SIZE = 19744) by reflexivity.
destruct (al_blocks _ _ LAWS _ _ _ _ _ pp PP_SIZE HAR Hin) as (_ & Hpp0 & Hppc & Happ & Hppr & _).
rewrite Erq in Hppc, Happ, Hppr.
remember (Ereg regs [Z_to_bv 64 7]) as E eqn:HE.
assert (HAE : forall n, (n < 32)%nat -> ew E n = ew (Ereg regs [Z_to_bv 64 7]) n) by (intros; subst E; reflexivity).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
  by (intros n r Hn; subst E; exact (ew_Ereg_nat regs _ n r Hn)).
assert (E32 : ew E 32 = Z_to_bv 64 7) by (subst E; exact (ew_Ereg_extra regs _ 0)).
assert (U9 : bv_unsigned (ew E 9) = R) by (rewrite (EE 9%nat (Z_to_bv 5 9) eq_refl), R9; apply unsigned_lit_small; lia).
assert (U21 : bv_unsigned (ew E 21) = pp + 0x4000)
  by (rewrite (EE 21%nat (Z_to_bv 5 21) eq_refl), R21; apply unsigned_lit_small; lia).
assert (U23 : bv_unsigned (ew E 23) = SHADOW_OFF)
  by (rewrite (EE 23%nat (Z_to_bv 5 23) eq_refl), R23; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U27 : bv_unsigned (ew E 27) = pp) by (rewrite (EE 27%nat (Z_to_bv 5 27) eq_refl), R27; apply unsigned_lit_small; lia).
assert (E21 : ew E 21 = Z_to_bv 64 (pp + 0x4000)) by (rewrite <- U21; symmetry; apply Z_to_bv_bv_unsigned).
assert (E23 : ew E 23 = Z_to_bv 64 SHADOW_OFF) by (rewrite <- U23; symmetry; apply Z_to_bv_bv_unsigned).
(* the symbolic state at B7 *)
assert (HS : st_ok rsegs E w3b_ss_b7 (restrict (w_H W) (mkst regs (Z_to_bv 64 W3B_B7) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. rewrite HE. unfold w3b_ss_b7. apply (entry_st_ok_full rsegs).
  - unfold w3b_regs_bo. apply regs_ok_rereg; [apply regs_ok_rereg; [apply regs_ok_Ereg | reflexivity |] | reflexivity |].
    + rewrite R10. reflexivity.
    + rewrite R11. unfold w64. cbn [sv_denot]. apply Z_to_bv64_eq_mod. reflexivity.
  - vm_compute. reflexivity.
  - rewrite <- HE. repeat apply Forall_cons; try apply Forall_nil.
    + unfold region_ok, w3b_slot_bo. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      * apply (chunk_ok_val rsegs E _ R 0x98 8 (SOff 32 0) (7 mod 2 ^ 64)); [| | cbn; lia | exact V98].
        -- cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. symmetry. apply Z_to_bv64_mod.
        -- split; [vm_compute; discriminate | vm_compute; reflexivity].
      * apply (chunk_ok_val rsegs E _ R 0xb0 8 w3b_shx (shadow_addr (pp + 0x4000) mod 2 ^ 64)); [| | cbn; lia | exact Vb0].
        -- unfold w3b_shx. rewrite denot_lit_U. apply Z_to_bv64_eq_mod.
           rewrite !U_SAlu. cbn [zalu_raw]. rewrite U_SLit, (U_atom E 21 (pp + 0x4000) E21) by lia.
           rewrite (U_atom E 23 SHADOW_OFF E23) by (unfold SHADOW_OFF; lia).
           change (Z.land (zcanon 3) 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
           unfold shadow_addr, zcanon, M64.
           assert (0 <= (pp + 0x4000) / 8 < 2 ^ 61) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
           rewrite (Z.mod_small ((pp + 0x4000) / 8)) by lia.
           rewrite (Z.mod_small ((pp + 0x4000) / 8 + SHADOW_OFF)) by (unfold SHADOW_OFF; lia).
           rewrite Z.mod_mod by lia. f_equal. lia.
        -- pose proof (Z.mod_pos_bound (shadow_addr (pp + 0x4000)) (2 ^ 64) ltac:(lia)). cbn. lia.
      * apply (chunk_ok_val rsegs E _ R 0xe8 8 (SLit W3B_M3FFD) (-0x3ffd mod 2 ^ 64));
        [reflexivity | split; [vm_compute; discriminate | vm_compute; reflexivity] | cbn; lia | exact Ve8].
    + unfold region_ok, w3b_hdr7_r. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U27. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable rsegs). apply (proj1 (Hppr (pp + o) ltac:(lia))).
    + unfold region_ok, w3b_len7_r. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U21. split; [lia|]. split; [lia|].
      split; [intros o Ho; apply (apresent_writable rsegs); apply (proj1 (Hppr (pp + 0x4000 + o) ltac:(lia)))|].
      constructor; [|constructor].
      apply (chunk_ok_val rsegs E _ (pp + 0x4000) 0 8 (SLit 4) 4);
        [reflexivity | split; [vm_compute; discriminate | vm_compute; reflexivity] | cbn; lia |].
      rewrite Z.add_0_r. exact Vlen.
  - rewrite <- HE. apply pairwise_disjoint_of_extents. unfold extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val w3b_slot_bo w3b_hdr7_r w3b_len7_r]. rewrite U9, U21, U27.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
  - rewrite <- HE. split; [|split; exact I]. cbn [f_atoms w3b_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U21, U27, U23. rewrite !Z.pow_0_r, !Z.mod_1_r. unfold W3B_PPHI, SHADOW_OFF. repeat split; lia. }
assert (SHOK : sh_ok rsegs w3b_Bx w3b_SH E (mrestrict (w_H W) memc)).
{ unfold sh_ok, w3b_SH. repeat apply Forall_cons; try apply Forall_nil;
  unfold shent_ok, app_apart, w3b_Bx; cbn [she_m she_lo she_hi];
  rewrite ?(U_atom E 23 SHADOW_OFF E23) by (unfold SHADOW_OFF; lia).
  - rewrite (U_atom E 27 pp) by (try (rewrite <- U27; symmetry; apply Z_to_bv_bv_unsigned); lia).
    split.
    + change (rd_of rsegs (mrestrict (w_H W) memc)) with (aview rsegs (w_H W) memc).
      apply (range_addressable_of_block rsegs B LAWS lyc Sc W memc mdc pp PP_SIZE); [exact HAR | exact Hin | lia | rewrite Erq; lia].
    + intros a Ha. unfold in_app, kLowShadowBeg, kHighMemBeg in Happ. unfold SHADOW_OFF. lia.
  - rewrite (U_atom E 21 (pp + 0x4000) E21) by lia.
    split.
    + change (rd_of rsegs (mrestrict (w_H W) memc)) with (aview rsegs (w_H W) memc).
      apply (range_addressable_of_block rsegs B LAWS lyc Sc W memc mdc pp PP_SIZE); [exact HAR | exact Hin | lia | rewrite Erq; lia].
    + intros a Ha. unfold in_app, kLowShadowBeg, kHighMemBeg in Happ. unfold SHADOW_OFF. lia. }
clear HE.
unfold cfg_at. change (w64 W3B_B7) with (Z_to_bv 64 W3B_B7).
aj_run_to_tok w3b_tbl7_ok HS HJ SHOK w3b_Bspan W3B_PH.
{ (* the run writes pp's header word and &pp->len: pp is a block of this segment's journal *)
  lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?sp ?fp ?b0 ?bc ?ly0 ?own0 =>
    let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk sp fp b0 bc ly0 own0) end.
  apply awr_ok_cons_ro; [cbn; lia|].
  eapply awr_ok_cons_gen; [reflexivity | exact U27 | | ].
  { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. replace a with (pp + (a - pp)) by lia.
    apply (rl_fresh_awr _ _ _ _ _ _ _ pp PP_SIZE); [exact Hin | exact Hout | rewrite Erq; lia]. }
  eapply awr_ok_cons_gen; [reflexivity | exact U21 | | apply awr_ok_nil].
  intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. replace a with (pp + (a - pp)) by lia.
  apply (rl_fresh_awr _ _ _ _ _ _ _ pp PP_SIZE); [exact Hin | exact Hout | rewrite Erq; lia]. }
(* ---- the state at 0x8051c ---- *)
pose proof (st_ok_mem_ok rsegs _ _ _ HS) as (_ & HOK & _). cbn [ss_mem] in HOK.
pose proof (Forall_inv (Forall_inv_tail HOK)) as (_ & _ & _ & Ch).
pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail HOK))) as (_ & _ & _ & Cl).
cbn [YP09.r_base YP09.r_chunks base_val] in Ch, Cl. rewrite U27 in Ch. rewrite U21 in Cl. clear HOK.
repeat rewrite Forall_cons_iff in Ch. repeat rewrite Forall_cons_iff in Cl.
destruct Cl as (Clen & _).
destruct Ch as (C7 & C6 & C5 & C4 & _).
rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ ms HS eq_refl) at 1.
apply (KONT (ms_regs ms) (ms_mem ms)).
- exact HJ.
- apply RPgCfgChanges.same_io_wvb.
- w3b_kept_regs HS HAE E ms regs [Z_to_bv 64 7] W.
- intros a Ha Ha1 Ha2. unfold aview, mbyte. rewrite (HFr (Z_to_bv 64 a)); [reflexivity|].
  rewrite unsigned_lit_small by lia. intros (rg & Hr & Hb).
  lazymatch type of Hr with In _ ?rs => let rs' := eval vm_compute in rs in change (In rg rs') in Hr end.
  repeat (destruct Hr as [<- | Hr];
    [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb; rewrite ?U27, ?U21 in Hb; lia | ]).
  destruct Hr.
- (* the four header bytes, one CVal 1 chunk each *)
  apply (proj2 (rm_bytes_aview rsegs (w_H W) (ms_mem ms) (pp + 4) (hdr_bytes 7))). intros i Hi. cbn in Hi.
  do 4 (destruct i as [|i];
    [ match goal with C : YP09.chunk_ok _ _ _ _ (YP09.mkChunk ?o (CVal 1 _)) |- _ =>
        eapply (w3b_chunk1 E (w_H W) ms pp o _ _ C);
        [ | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia];
        cbn [sv_denot]; rewrite ?E32; vm_compute; reflexivity end | ]); lia.
- (* len = 8 *)
  apply rm_bytes_of_val. rewrite <- (Z.add_0_r (pp + 16384)).
  exact (val_of_chunk_ok rsegs E _ (pp + 16384) 0 8 (SLit 8) 8 Clen eq_refl
    ltac:(split; [vm_compute; discriminate | vm_compute; reflexivity]) ltac:(cbn; lia)).
Qed.

(* ===================================== the block's bytes at PH =====================================
   pc_image of the empty record of shape sh (sh <> 7): BO's image (the top size word only) with the twelve header
   bytes at 4, len = 16 at 0x4000 and is_props at 0x4008. *)
Lemma w3b_img_ph : forall sh, 0 <= sh <= 6 ->
pc_image (PbCut sh [] None) =
overwrite (rm_slice rs_img_hdr 0 16384) 4 (hdr_bytes sh) ++ le64 16 ++ le32 (Z.b2z (negb (sh =? 6))) ++
rm_slice rs_img_hdr 16396 3348.
Proof.
intros sh Hsh. assert (H : sh = 0 \/ sh = 1 \/ sh = 2 \/ sh = 3 \/ sh = 4 \/ sh = 5 \/ sh = 6) by lia.
destruct H as [->|[->|[->|[->|[->|[->| ->]]]]]]; vm_compute; reflexivity.
Qed.
Lemma w3b_len_hdr : forall sh, sh <> 7 -> length (hdr_bytes sh) = 12%nat.
Proof. intros sh Hsh. unfold hdr_bytes. rewrite (proj2 (Z.eqb_neq sh 7) Hsh). reflexivity. Qed.
Lemma w3b_ph_img : forall H mem H' mem' pp sh, 0 <= sh <= 6 ->
rm_bytes rsegs H mem pp rs_img_hdr ->
rm_bytes rsegs H' mem' (pp + 4) (hdr_bytes sh) ->
rm_bytes rsegs H' mem' (pp + 16384) (le64 16) ->
rm_bytes rsegs H' mem' (pp + 16392) (le32 (Z.b2z (negb (sh =? 6)))) ->
(forall y, pp <= y < pp + 19744 -> ~ (pp + 4 <= y < pp + 16) -> ~ (pp + 16384 <= y < pp + 16396) ->
 aview rsegs H' mem' y = aview rsegs H mem y) ->
rm_bytes rsegs H' mem' pp (pc_image (PbCut sh [] None)).
Proof.
intros H mem H' mem' pp sh Hsh B0 Bh Bl Bi K.
rewrite (w3b_img_ph sh Hsh).
assert (L0 : length rs_img_hdr = 19744%nat) by (vm_compute; reflexivity).
assert (L1 : length (rm_slice rs_img_hdr 0 16384) = 16384%nat) by (vm_compute; reflexivity).
assert (L2 : length (rm_slice rs_img_hdr 16396 3348) = 3348%nat) by (vm_compute; reflexivity).
pose proof (w3b_len_hdr sh ltac:(lia)) as Lh.
assert (Lo : length (overwrite (rm_slice rs_img_hdr 0 16384) 4 (hdr_bytes sh)) = 16384%nat)
  by (rewrite length_overwrite; [exact L1 | rewrite Lh, L1; apply Nat.leb_le; vm_compute; reflexivity]).
apply rm_bytes_app. split.
- pose proof (rm_bytes_slice rsegs H mem pp rs_img_hdr 0 16384 B0
    ltac:(rewrite L0; apply Nat.leb_le; vm_compute; reflexivity)) as Bb.
  change (Z.of_nat 0) with 0 in Bb. rewrite Z.add_0_r in Bb.
  apply (rm_bytes_patch rsegs H mem H' mem' pp _ 4 _ Bb);
    [exact Bh | rewrite Lh, L1; apply Nat.leb_le; vm_compute; reflexivity |].
  rewrite Lh, L1. intros y Hy Hn. change (Z.of_nat 16384) with 16384 in Hy.
  change (Z.of_nat 4) with 4 in Hn. change (Z.of_nat (4 + 12)) with 16 in Hn. apply K; lia.
- rewrite Lo. change (Z.of_nat 16384) with 16384. apply rm_bytes_app. split; [exact Bl|].
  change (length (le64 16)) with 8%nat. change (Z.of_nat 8) with 8. apply rm_bytes_app. split.
  + replace (pp + 16384 + 8) with (pp + 16392) by lia. exact Bi.
  + change (length (le32 (Z.b2z (negb (sh =? 6))))) with 4%nat. change (Z.of_nat 4) with 4.
    pose proof (rm_bytes_slice rsegs H mem pp rs_img_hdr 16396 3348 B0
      ltac:(rewrite L0; apply Nat.leb_le; vm_compute; reflexivity)) as Bt.
    change (Z.of_nat 16396) with 16396 in Bt. replace (pp + 16384 + 8 + 4) with (pp + 16396) by lia.
    apply (rm_bytes_kept rsegs H mem H' mem' _ _ Bt). rewrite L2. change (Z.of_nat 3348) with 3348.
    intros y Hy. apply K; lia.
Qed.

(* pc_image of the empty record of shape 7: BO's image with the Struct word at 4 and len = 8 at 0x4000 *)
Lemma w3b_img_b7 :
pc_image (PbCut 7 [] None) =
overwrite (rm_slice rs_img_hdr 0 16384) 4 (hdr_bytes 7) ++ le64 8 ++ rm_slice rs_img_hdr 16392 3352.
Proof. vm_compute. reflexivity. Qed.
Lemma w3b_b7_img : forall H mem H' mem' pp,
rm_bytes rsegs H mem pp rs_img_hdr ->
rm_bytes rsegs H' mem' (pp + 4) (hdr_bytes 7) ->
rm_bytes rsegs H' mem' (pp + 16384) (le64 8) ->
(forall y, pp <= y < pp + 19744 -> ~ (pp + 4 <= y < pp + 8) -> ~ (pp + 16384 <= y < pp + 16392) ->
 aview rsegs H' mem' y = aview rsegs H mem y) ->
rm_bytes rsegs H' mem' pp (pc_image (PbCut 7 [] None)).
Proof.
intros H mem H' mem' pp B0 Bh Bl K.
rewrite w3b_img_b7.
assert (L0 : length rs_img_hdr = 19744%nat) by (vm_compute; reflexivity).
assert (L1 : length (rm_slice rs_img_hdr 0 16384) = 16384%nat) by (vm_compute; reflexivity).
assert (L2 : length (rm_slice rs_img_hdr 16392 3352) = 3352%nat) by (vm_compute; reflexivity).
assert (Lh : length (hdr_bytes 7) = 4%nat) by reflexivity.
assert (Lo : length (overwrite (rm_slice rs_img_hdr 0 16384) 4 (hdr_bytes 7)) = 16384%nat)
  by (rewrite length_overwrite; [exact L1 | rewrite Lh, L1; apply Nat.leb_le; vm_compute; reflexivity]).
apply rm_bytes_app. split.
- pose proof (rm_bytes_slice rsegs H mem pp rs_img_hdr 0 16384 B0
    ltac:(rewrite L0; apply Nat.leb_le; vm_compute; reflexivity)) as Bb.
  change (Z.of_nat 0) with 0 in Bb. rewrite Z.add_0_r in Bb.
  apply (rm_bytes_patch rsegs H mem H' mem' pp _ 4 _ Bb);
    [exact Bh | rewrite Lh, L1; apply Nat.leb_le; vm_compute; reflexivity |].
  rewrite Lh, L1. intros y Hy Hn. change (Z.of_nat 16384) with 16384 in Hy.
  change (Z.of_nat 4) with 4 in Hn. change (Z.of_nat (4 + 4)) with 8 in Hn. apply K; lia.
- rewrite Lo. change (Z.of_nat 16384) with 16384. apply rm_bytes_app. split; [exact Bl|].
  change (length (le64 8)) with 8%nat. change (Z.of_nat 8) with 8.
  pose proof (rm_bytes_slice rsegs H mem pp rs_img_hdr 16392 3352 B0
    ltac:(rewrite L0; apply Nat.leb_le; vm_compute; reflexivity)) as Bt.
  change (Z.of_nat 16392) with 16392 in Bt. replace (pp + 16384 + 8) with (pp + 16392) by lia.
  apply (rm_bytes_kept rsegs H mem H' mem' _ _ Bt). rewrite L2. change (Z.of_nat 3352) with 3352.
  intros y Hy. apply K; lia.
Qed.

(* ===================================== the piece statements =====================================  *)
Section e.
Variable MT : ameter_ops.

Ltac w3b_in_kept := unfold W3B_KEPT_BO; cbn [In]; lia.

(* BO -> PH *)
Lemma rs_piece_W3b_hdr : rs_piece_W3b_hdr_stmt rsegs B MT.
Proof.
intros cx POST rest HST HPH ly2 S2 W2 regs2 mem2 md2 r sh np [HC Hsh7].
pose proof (AR_laws_ok rsegs B) as LAWS.
destruct HST as (HPRE & _ & _ & _).
pose proof HPRE as (HJc & _ & _ & _ & _ & HSe & _ & HRsz & HRstk & Hown & HFe & _ & _ & Hppc & _ & _ & _ & _ & _ & _ & _
  & Hfresh).
cbn [hi_rsz hi_cid role_himg_A] in HRsz, Hown, HFe.
destruct HC as (HCORE & HAT & HFSH & HPP & HIN & HSUF & Esh & Enp & Er).
pose proof HCORE as (HJ & H234 & Hfr & Hperm & Hio & Hmo & Hkeep).
(* the bounds of R, pp and F *)
pose proof HJc as (HARc & _ & _ & _ & _ & Hfrsc & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (_ & HSTK0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & _ & _ & _ & _).
assert (HT : T_SEG_STK = 16384) by reflexivity.
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HARc Hppc) as (_ & Hpp0 & Hppcl & Happ & _ & _).
change (req_size PP_SIZE) with 19744 in Hppcl, Happ.
assert (HFin : In (3, x_pos rsegs cx) (frames (x_Sc rsegs cx))) by (rewrite Hfrsc; apply in_or_app; left; exact Hown).
destruct (frames_bounds rsegs B LAWS _ _ _ _ _ _ _ HARc HFin) as (HF0 & HFc & _).
rewrite <- HFe in HF0, HFc. change (fs_frame_bytes 3) with 512 in HFc.
assert (Hsh : 0 <= sh <= 6)
  by (assert (0 <= sh < 8) by (rewrite Esh; unfold rs_sh; apply Z.mod_pos_bound; lia); lia).
assert (Hin2 : In (e_pp (x_e rsegs cx), PP_SIZE) (ablocks B ly2 S2))
  by (eapply Permutation_in; [apply Permutation_sym; exact Hperm | exact Hppc]).
(* the facts of BO's location list *)
unfold rs_at_cx, rs_at, rs_L_hdr, rs_cur2 in HAT. cbn [app] in HAT.
pose proof (Forall_inv_tail (Forall_inv_tail HAT)) as HATph.
repeat rewrite Forall_cons_iff in HAT.
destruct HAT as (A10 & A11 & A15 & A16 & A20 & A8 & A9 & A19 & A23 & A21 & A22 & A25 & A27 & C30 & C90 & C98 & Cb0
  & Ce8 & Cc8 & Cf8 & _).
cbn [fst snd rl_at rl_xv] in A10, A11, A9, A21, A23, A27, C98, Cb0, Ce8.
pose proof (rm_pp_len rsegs (le32 0) false false false [] false ltac:(unfold POD_BUF_MAX; rewrite length_le32; lia)
  ltac:(cbn; lia) ltac:(constructor) (w_H W2) mem2 (e_pp (x_e rsegs cx)) HPP) as Vlen.
unfold OFF_LEN in Vlen. rewrite length_le32 in Vlen. cbn [Z.of_nat Pos.of_succ_nat] in Vlen.
eapply (w3b_hdr_core _ _ _ _ _ _ _ _ _ ly2 S2 W2 mem2 md2 _ regs2 (e_R (x_e rsegs cx)) (e_pp (x_e rsegs cx)) sh POST
  HJ Hin2 Hfresh); try eassumption; try lia.
intros regs3 mem3 md3 HJ3 Hio3 HK3 HM3 Bh Bl Bi.
apply (HPH ly2 S2 W2 regs3 mem3 md3 r sh np).
unfold rs_cut_PH. split; [|split; [|split; [|split]]].
- (* the journal and the kept bytes *)
  unfold rs_core, rs_mid. split; [exact HJ3|].
  split; [intros rr Hrr; rewrite <- (H234 rr Hrr); destruct Hrr as [->|[->| ->]]; apply HK3; w3b_in_kept|].
  split; [exact Hfr|]. split; [exact Hperm|]. split; [eapply same_io_trans; [exact Hio | exact Hio3]|].
  split; [exact Hmo|].
  intros a Ha HnS HnE. rewrite <- (Hkeep a Ha HnS HnE).
  apply HM3; [exact Ha | |]; intros X; apply HnE; right; unfold PP_SIZE; lia.
- (* PH's location list: BO's without a0 and a1, each kept *)
  unfold rs_at_cx, rs_at. apply (rm_atl_kept rsegs (w_H W2) mem2 (w_H W2) mem3 regs2 regs3 _ _ HATph).
  intros f Hf. try unfold rs_L_PH, rs_cur2 in Hf. cbn [In app] in Hf.
  repeat (destruct Hf as [<-|Hf];
    [cbn [rm_keeps fst rl_xv]; first [apply HK3; w3b_in_kept | intros i Hi; apply HM3; lia] |]).
  destruct Hf.
- (* the frame's shadow: no byte of it is written *)
  apply (rm_fsh_kept rsegs (w_H W2) mem2 (w_H W2) mem3 _ rs_P0 HFSH).
  intros i Hi. change (length rs_P0) with 52%nat in Hi.
  assert (0 <= e_F (x_e rsegs cx) / 8 <= 17592184995840)
    by (split; [apply Z.div_pos; lia | apply (Z.div_le_mono _ 0x7fffff800000 8); lia]).
  unfold in_app, kLowShadowBeg, kHighMemBeg in Happ.
  apply HM3; unfold shadow_addr, SHADOW_OFF; lia.
- (* the block holds the empty record of this shape *)
  apply (w3b_ph_img (w_H W2) mem2 (w_H W2) mem3 _ sh Hsh HPP Bh Bl Bi).
  intros y Hy Hn1 Hn2. apply HM3; lia.
- split; [exact HIN|]. split; [exact HSUF|]. split; [exact Esh|]. split; [exact Enp | exact Er].
Qed.

(* B7 -> PH *)
Lemma rs_piece_W3b_b7 : rs_piece_W3b_b7_stmt rsegs B MT.
Proof.
intros cx POST rest HST HPH ly2 S2 W2 regs2 mem2 md2 r np HC.
pose proof (AR_laws_ok rsegs B) as LAWS.
destruct HST as (HPRE & _ & _ & _).
pose proof HPRE as (HJc & _ & _ & _ & _ & HSe & _ & HRsz & HRstk & Hown & HFe & _ & _ & Hppc & _ & _ & _ & _ & _ & _ & _
  & Hfresh).
cbn [hi_rsz hi_cid role_himg_A] in HRsz, Hown, HFe.
destruct HC as (HCORE & HAT & HFSH & HPP & HIN & HSUF & Esh & Enp & Er).
pose proof HCORE as (HJ & H234 & Hfr & Hperm & Hio & Hmo & Hkeep).
(* the bounds of R, pp and F *)
pose proof HJc as (HARc & _ & _ & _ & _ & Hfrsc & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (_ & HSTK0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & _ & _ & _ & _).
assert (HT : T_SEG_STK = 16384) by reflexivity.
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HARc Hppc) as (_ & Hpp0 & Hppcl & Happ & _ & _).
change (req_size PP_SIZE) with 19744 in Hppcl, Happ.
assert (HFin : In (3, x_pos rsegs cx) (frames (x_Sc rsegs cx))) by (rewrite Hfrsc; apply in_or_app; left; exact Hown).
destruct (frames_bounds rsegs B LAWS _ _ _ _ _ _ _ HARc HFin) as (HF0 & HFc & _).
rewrite <- HFe in HF0, HFc. change (fs_frame_bytes 3) with 512 in HFc.
assert (Hin2 : In (e_pp (x_e rsegs cx), PP_SIZE) (ablocks B ly2 S2))
  by (eapply Permutation_in; [apply Permutation_sym; exact Hperm | exact Hppc]).
(* the facts of B7's location list (BO's, with the shape 7) *)
unfold rs_at_cx, rs_at, rs_L_hdr, rs_cur2 in HAT. cbn [app] in HAT.
pose proof (Forall_inv_tail (Forall_inv_tail HAT)) as HATph.
repeat rewrite Forall_cons_iff in HAT.
destruct HAT as (A10 & A11 & A15 & A16 & A20 & A8 & A9 & A19 & A23 & A21 & A22 & A25 & A27 & C30 & C90 & C98 & Cb0
  & Ce8 & Cc8 & Cf8 & _).
cbn [fst snd rl_at rl_xv] in A10, A11, A9, A21, A23, A27, C98, Cb0, Ce8.
pose proof (rm_pp_len rsegs (le32 0) false false false [] false ltac:(unfold POD_BUF_MAX; rewrite length_le32; lia)
  ltac:(cbn; lia) ltac:(constructor) (w_H W2) mem2 (e_pp (x_e rsegs cx)) HPP) as Vlen.
unfold OFF_LEN in Vlen. rewrite length_le32 in Vlen. cbn [Z.of_nat Pos.of_succ_nat] in Vlen.
eapply (w3b_b7_core _ _ _ _ _ _ _ _ _ ly2 S2 W2 mem2 md2 _ regs2 (e_R (x_e rsegs cx)) (e_pp (x_e rsegs cx)) POST
  HJ Hin2 Hfresh); try eassumption; try lia.
intros regs3 mem3 md3 HJ3 Hio3 HK3 HM3 Bh Bl.
apply (HPH ly2 S2 W2 regs3 mem3 md3 r 7 np).
unfold rs_cut_PH. split; [|split; [|split; [|split]]].
- (* the journal and the kept bytes *)
  unfold rs_core, rs_mid. split; [exact HJ3|].
  split; [intros rr Hrr; rewrite <- (H234 rr Hrr); destruct Hrr as [->|[->| ->]]; apply HK3; w3b_in_kept|].
  split; [exact Hfr|]. split; [exact Hperm|]. split; [eapply same_io_trans; [exact Hio | exact Hio3]|].
  split; [exact Hmo|].
  intros a Ha HnS HnE. rewrite <- (Hkeep a Ha HnS HnE).
  apply HM3; [exact Ha | |]; intros X; apply HnE; right; unfold PP_SIZE; lia.
- (* PH's location list: B7's without a0 and a1, each kept *)
  unfold rs_at_cx, rs_at. apply (rm_atl_kept rsegs (w_H W2) mem2 (w_H W2) mem3 regs2 regs3 _ _ HATph).
  intros f Hf. try unfold rs_L_PH, rs_cur2 in Hf. cbn [In app] in Hf.
  repeat (destruct Hf as [<-|Hf];
    [cbn [rm_keeps fst rl_xv]; first [apply HK3; w3b_in_kept | intros i Hi; apply HM3; lia] |]).
  destruct Hf.
- (* the frame's shadow: no byte of it is written *)
  apply (rm_fsh_kept rsegs (w_H W2) mem2 (w_H W2) mem3 _ rs_P0 HFSH).
  intros i Hi. change (length rs_P0) with 52%nat in Hi.
  assert (0 <= e_F (x_e rsegs cx) / 8 <= 17592184995840)
    by (split; [apply Z.div_pos; lia | apply (Z.div_le_mono _ 0x7fffff800000 8); lia]).
  unfold in_app, kLowShadowBeg, kHighMemBeg in Happ.
  apply HM3; unfold shadow_addr, SHADOW_OFF; lia.
- (* the block holds the empty record of shape 7 *)
  apply (w3b_b7_img (w_H W2) mem2 (w_H W2) mem3 _ HPP Bh Bl).
  intros y Hy Hn1 Hn2. apply HM3; lia.
- split; [exact HIN|]. split; [exact HSUF|]. split; [exact Esh|]. split; [exact Enp | exact Er].
Qed.
End e.
End d.
End b.
