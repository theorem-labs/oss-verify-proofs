(* diginet_seg7 (diginet_codec.c:308-335) at image A 0x860b4, 27 instructions, real frame 16.
   a0 holds the character c; i = (c - 32) mod 256. For i > 90 the function returns -1 (0x86100);
   otherwise it reads the word i of the 364-byte table the compiler made for the switch (image A
   0x213a0) and returns it sign-extended.
   The read is instrumented: 0x860cc-0x860d8 load the shadow offset (the .got slot of the cell and
   the cell itself, the two base regions of lib/A/Prog/CPgWalk.v), 0x860e8-0x860f0 load the shadow
   byte k of the address a = 0x213a0 + 4 i, and 0x860f4 / 0x86110-0x86118 continue to the load at
   0x860f8 when k = 0 or (a mod 8) + 3 < k. The token layer of lib/Reusable/YCbn.v decides both
   from one obligation, range_addressable of [a, a + 4), which the contract's crd_ok premise of the
   whole table pays; the error path at 0x8611c is not reached.
   The load itself is at an address the engine cannot split into an atom and a literal, so the walk
   names it: it puts a in a fresh atom with a one-chunk read-only region whose value is the table
   word, read from the image through the contract's arodata_okP / in_roP premises. *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw0 ACef AF0l ACej ACeh ACem ACep.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw1 AWalkFw2 ACfm.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase CPgEncC CPgWalk.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ============================ the index and the table ============================ *)
(* the index the code forms from the low byte of a0 *)
Definition seg7_idx (c : Z) : Z := (c mod 256 - 32) mod 256.
(* the table word of the index, as the unsigned 32-bit value the four bytes hold *)
Definition seg7_word (i : Z) : Z := nth (Z.to_nat i) seg7_table (-1) mod 2 ^ 32.

Lemma seg7_idx_range : forall c, 0 <= seg7_idx c < 256.
Proof. intros c. unfold seg7_idx. apply Z.mod_pos_bound. lia. Qed.

(* `addi a0,a0,-32` then `zext.b a0,a0` *)
Lemma seg7_idx_land : forall c, Z.land ((c + -32) mod 2 ^ 64) 255 = seg7_idx c.
Proof.
intros c. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. change (2 ^ 8) with 256.
rewrite <- (Znumtheory.Zmod_div_mod 256 (2 ^ 64) (c + -32) ltac:(lia) ltac:(lia)
  ltac:(exists (2 ^ 56); vm_compute; reflexivity)).
unfold seg7_idx. rewrite Zminus_mod_idemp_l. f_equal; lia.
Qed.

Lemma seg7_spec_big : forall c, 90 < seg7_idx c -> seg7_spec (c mod 256) = -1.
Proof.
intros c H. unfold seg7_spec. cbv zeta. fold (seg7_idx c).
rewrite (proj2 (Z.leb_gt (seg7_idx c) 90)) by lia. reflexivity.
Qed.

Lemma seg7_spec_small : forall c, seg7_idx c <= 90 ->
seg7_spec (c mod 256) = nth (Z.to_nat (seg7_idx c)) seg7_table (-1).
Proof.
intros c H. unfold seg7_spec. cbv zeta. fold (seg7_idx c).
rewrite (proj2 (Z.leb_le (seg7_idx c) 90)) by lia. reflexivity.
Qed.

(* every entry of the table is a signed byte *)
Definition seg7_entries_chk : bool :=
forallb (fun p => (-1 <=? nth p seg7_table (-1)) && (nth p seg7_table (-1) <=? 127)) (seq 0 91).
Lemma seg7_entries_chk_ok : seg7_entries_chk = true.
Proof. vm_compute. reflexivity. Qed.
Lemma seg7_entry_range : forall i, 0 <= i <= 90 -> -1 <= nth (Z.to_nat i) seg7_table (-1) <= 127.
Proof.
intros i Hi. pose proof seg7_entries_chk_ok as H. unfold seg7_entries_chk in H.
pose proof (proj1 (forallb_forall _ _) H (Z.to_nat i) ltac:(apply in_seq; lia)) as H1. cbv beta in H1.
apply andb_prop in H1 as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. lia.
Qed.

Lemma seg7_word_mod : forall i, seg7_word i mod 2 ^ 32 = seg7_word i.
Proof. intros i. unfold seg7_word. rewrite Z.mod_mod by lia. reflexivity. Qed.

(* the sign-extension of the loaded word is the table entry *)
Lemma seg7_swrap : forall i, 0 <= i <= 90 ->
bv_swrap 32 (seg7_word i) = nth (Z.to_nat i) seg7_table (-1).
Proof.
intros i Hi. pose proof (seg7_entry_range i Hi) as Hv.
set (v := nth (Z.to_nat i) seg7_table (-1)) in *.
unfold seg7_word, bv_swrap, bv_wrap. fold v.
change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
rewrite Zplus_mod_idemp_l. rewrite (Z.mod_small (v + 2 ^ 31)) by lia. lia.
Qed.

(* the 364 bytes of the table in the image file are the words of DgnLib's seg7_table *)
Definition seg7_rom_chk : bool :=
forallb (fun p =>
  forallb (fun k =>
    match seg_rom tfibsegs (Z_to_bv 64 (CA_SEG7 + 4 * Z.of_nat p + Z.of_nat k)) with
    | Some b => Z.eqb (bv_unsigned b) (seg7_word (Z.of_nat p) / 2 ^ (8 * Z.of_nat k) mod 256)
    | None => false
    end) (seq 0 4)) (seq 0 91).
Lemma seg7_rom_chk_ok : seg7_rom_chk = true.
Proof. vm_compute. reflexivity. Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* the table word, as the engine's four little-endian bytes of the read-only data *)
Lemma seg7_rd32 : forall (H : word -> bool) (m : word -> option byte) i,
0 <= i <= 90 ->
(forall a, CA_SEG7 <= a < CA_SEG7 + 364 ->
 aview tfibsegs H m a = option_map (fun b : byte => bv_unsigned b) (seg_rom tfibsegs (Z_to_bv 64 a))) ->
rd32 (aview tfibsegs H m) (CA_SEG7 + 4 * i) (seg7_word i).
Proof.
intros H m i Hi Hrom k Hk.
pose proof seg7_rom_chk_ok as Hc. unfold seg7_rom_chk in Hc.
pose proof (proj1 (forallb_forall _ _) Hc (Z.to_nat i) ltac:(apply in_seq; lia)) as H1. cbv beta in H1.
pose proof (proj1 (forallb_forall _ _) H1 k ltac:(apply in_seq; lia)) as H2. cbv beta in H2.
rewrite Z2Nat.id in H2 by lia.
rewrite (Hrom (CA_SEG7 + 4 * i + Z.of_nat k) ltac:(unfold CA_SEG7 in *; lia)).
destruct (seg_rom tfibsegs (Z_to_bv 64 (CA_SEG7 + 4 * i + Z.of_nat k))) as [b|] eqn:Eb; [|discriminate].
apply Z.eqb_eq in H2. cbn [option_map]. f_equal. rewrite H2.
first [unfold YG0f.le_byte | unfold YO0f.le_byte].
change (8 * Z.of_nat 4) with 32. unfold seg7_word. rewrite Z.mod_mod by lia.
rewrite Z.shiftr_div_pow2 by lia. reflexivity.
Qed.

(* the table word, as the one-chunk read-only region the walk gives the load *)
Lemma seg7_tbl_region_ok : forall (E : env) (W : world tfibsegs) (m : word -> option byte) (i : Z),
0 <= i <= 90 -> ew E 40 = Z_to_bv 64 (CA_SEG7 + 4 * i) -> ew E 41 = Z_to_bv 64 (seg7_word i) ->
(forall a, CA_SEG7 <= a < CA_SEG7 + 364 ->
 aview tfibsegs (w_H W) m a = option_map (fun b : byte => bv_unsigned b) (seg_rom tfibsegs (Z_to_bv 64 a))) ->
region_ok tfibsegs E (mrestrict (w_H W) m)
  (YP09.mkRegion (Some 40%nat) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SOff 41 0))]).
Proof.
intros E W m i Hi E40 E41 Hrom.
assert (Hw : 0 <= seg7_word i < 2 ^ 32) by (unfold seg7_word; apply Z.mod_pos_bound; lia).
unfold region_ok.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite E40, (unsigned_lit_small (CA_SEG7 + 4 * i) ltac:(unfold CA_SEG7; lia)).
split; [unfold CA_SEG7; lia|]. split; [unfold CA_SEG7; lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil].
apply (chunk_ok_val tfibsegs E (mrestrict (w_H W) m) (CA_SEG7 + 4 * i) 0 4 (SOff 41 0) (seg7_word i)).
- rewrite sv_denot_SOff0. exact E41.
- change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32). lia.
- cbn. lia.
- rewrite Z.add_0_r. change (N.to_nat 4) with 4%nat.
  apply (val_mem_of_rd32 tfibsegs (w_H W) m). apply seg7_rd32; [lia | exact Hrom].
Qed.

(* the index and the address the code forms, as the engine's values *)
Lemma cdc_U_idx : forall E c, 0 <= c < 2 ^ 64 -> ew E 10 = Z_to_bv 64 c ->
U E (SAlu ALU_AND (SOff 10 (-32)) (SLit 255)) = seg7_idx c.
Proof.
intros E c Hc H10. rewrite U_and_lit by lia. rewrite U_SOff, H10.
rewrite (unsigned_lit_small c Hc). unfold zcanon, M64. apply seg7_idx_land.
Qed.
Lemma cdc_U_sh : forall E c, 0 <= c < 2 ^ 64 -> ew E 10 = Z_to_bv 64 c ->
U E (SAlu ALU_SLL (SAlu ALU_AND (SOff 10 (-32)) (SLit 255)) (SLit 2)) = 4 * seg7_idx c.
Proof.
intros E c Hc H10. pose proof (seg7_idx_range c) as Hi.
rewrite U_SAlu. cbn [zalu_raw]. rewrite (cdc_U_idx E c Hc H10), U_SLit.
change (Z.land (zcanon 2) 63) with 2. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4.
unfold zcanon, M64. rewrite Z.mod_small by lia. lia.
Qed.
Lemma cdc_U_x : forall E c, 0 <= c < 2 ^ 64 -> ew E 10 = Z_to_bv 64 c ->
U E (SAlu ALU_ADD (SLit 136096) (SAlu ALU_SLL (SAlu ALU_AND (SOff 10 (-32)) (SLit 255)) (SLit 2)))
= CA_SEG7 + 4 * seg7_idx c.
Proof.
intros E c Hc H10. pose proof (seg7_idx_range c) as Hi.
rewrite U_SAlu. cbn [zalu_raw]. rewrite (cdc_U_sh E c Hc H10), (U_lit E 136096 ltac:(lia)).
unfold zcanon, M64, CA_SEG7. rewrite Z.mod_small by lia. reflexivity.
Qed.

(* the table's region lies off the save area, the .got slot and the shadow-offset cell *)
Lemma seg7_tbl_disj : forall (E : env) (i sp : Z) (ch : list YP09.chunk),
0 <= i <= 90 -> ew E 40 = Z_to_bv 64 (CA_SEG7 + 4 * i) -> bv_unsigned (ew E 2) = sp -> 2 ^ 46 + 16 <= sp ->
all_disjoint E (YP09.mkRegion (Some 40%nat) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SOff 41 0))])
  [YP09.mkRegion (Some 2%nat) (-16) 0 (-16) 0 ch;
   YP09.mkRegion None 645904 645912 0 0 [YP09.mkChunk 645904 (CVal 8 (SLit 681080))];
   YP09.mkRegion None 681080 681088 0 0 [YP09.mkChunk 681080 (CVal 8 (SOff 32 0))]].
Proof.
intros E i sp ch Hi E40 E2 Hsp.
cbn [all_disjoint]. unfold extent_disjoint, base_val.
cbn [YP09.r_base YP09.r_lo YP09.r_hi].
rewrite E40, (unsigned_lit_small (CA_SEG7 + 4 * i) ltac:(unfold CA_SEG7; lia)), E2.
unfold CA_SEG7. repeat split; try exact I; lia.
Qed.

(* the check's obligation: the four bytes of the table entry are marked usable *)
Lemma seg7_obl : forall (E : env) (W : world tfibsegs) (m m' : word -> option byte) (c : Z),
0 <= c < 2 ^ 64 -> ew E 10 = Z_to_bv 64 c -> ew E 32 = Z_to_bv 64 SB -> seg7_idx c <= 90 ->
range_addressable (aview tfibsegs (w_H W) m) SHADOW_OFF CA_SEG7 364 ->
(forall x, CA_SEG7 <= x < CA_SEG7 + 364 ->
 aview tfibsegs (w_H W) m' (shadow_of_addr SHADOW_OFF x) = aview tfibsegs (w_H W) m (shadow_of_addr SHADOW_OFF x)) ->
range_addressable (rd_of tfibsegs (mrestrict (w_H W) m')) (U E CW_Bx)
  (U E (SAlu ALU_ADD (SLit 136096) (SAlu ALU_SLL (SAlu ALU_AND (SOff 10 (-32)) (SLit 255)) (SLit 2)))) 4.
Proof.
intros E W m m' c Hc E10 E32 Hle Hra Hag.
pose proof (seg7_idx_range c) as Hidx.
apply (obl_of_range tfibsegs (w_H W) m' E CW_Bx _ 4 CA_SEG7 364).
- apply (range_addressable_agree (aview tfibsegs (w_H W) m) (aview tfibsegs (w_H W) m')
    SHADOW_OFF CA_SEG7 364); [exact Hag | exact Hra].
- exact (cw_U_Bx E E32).
- rewrite (cdc_U_x E c Hc E10). unfold CA_SEG7. lia.
- rewrite (cdc_U_x E c Hc E10). unfold CA_SEG7. lia.
Qed.

Context {SK : YI16.sink_head}.
Section d.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis ML : model_laws (as_universe B).
Variables RLO RHI : Z.

Theorem diginet_seg7_A_holds : cdc_seg7_specX tfibsegs B MT RLO RHI CA_SEG7 0x860b4.
Proof using MTL TL LAWS ML.
unfold cdc_seg7_specX.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs c HE H10 Hc HRO HinRO HCRD.
pose proof Hwx_tfa as Hwx. pose proof tfib_segs_low as Hsegs.
pose proof (seg7_idx_range c) as Hidx.
pose proof (cw_entry_stack B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs T_seg7 HE
  ltac:(unfold T_seg7; lia)) as (Hceil & H47 & H46 & Hal16 & Hpres).
pose proof (cw_entry_base B TL LAWS 0x860b4 16 [] STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k
  regs T_seg7 HE ltac:(unfold T_seg7; lia) ltac:(vm_compute; reflexivity)) as HS.
destruct HE as (HJ & Hra & Hra4 & Hgp & Htp & Hal16' & Hwlo & Hwhi & Hev & Hlive).
cw_keep_j0 HJ HJ0.
assert (H46' : 2 ^ 46 + 16 <= spZ regs) by (unfold T_seg7 in H46; lia).
assert (Hwlo16 : sp0 - STK <= spZ regs - 16) by (unfold T_seg7 in Hwlo; lia).
(* the table's bytes are the image's, in the call's own state *)
assert (HROMc : forall a, CA_SEG7 <= a < CA_SEG7 + 364 ->
  aview tfibsegs (w_H W) memc a = option_map (fun b : byte => bv_unsigned b) (seg_rom tfibsegs (Z_to_bv 64 a))).
{ intros a Ha.
  assert (Hlc : lib_const_addr a) by (unfold lib_const_addr, CA_SEG7 in *; right; right; left; lia).
  destruct (tl_lib_consts B TL a Hlc) as [Hown Herr].
  apply HRO; [| exact Hown | exact Herr].
  replace a with (CA_SEG7 + (a - CA_SEG7)) by lia. apply HinRO. lia. }
assert (HCRDra : range_addressable (aview tfibsegs (w_H W) memc) SHADOW_OFF CA_SEG7 364)
  by (destruct HCRD as (_ & _ & _ & Hra' & _); exact Hra').
remember (Ereg regs (cw_extra [])) as E eqn:HEq.
assert (HAE : env_agree 32 (Ereg regs (cw_extra [])) E) by (subst E; apply env_agree_refl).
assert (E1 : ew E 1 = getr regs 1) by (subst E; exact (cw_ew_reg regs [] 1 1%bv eq_refl)).
assert (B2 : bv_unsigned (ew E 2) = spZ regs)
  by (subst E; rewrite (cw_ew_reg regs [] 2 2%bv eq_refl); reflexivity).
assert (E10 : ew E 10 = Z_to_bv 64 c) by (subst E; rewrite (cw_ew_reg regs [] 10 10%bv eq_refl); exact H10).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; apply cw_ew_SB).
clear HEq.
assert (SHOK : sh_ok tfibsegs CW_Bx [] E (mrestrict (w_H W) memc)) by constructor.
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 16 <= a < spZ regs) ->
  aview tfibsegs (w_H W) memc a = aview tfibsegs (w_H W) memc a) by (intros; reflexivity).
unfold cfg_at. change (w64 0x860b4) with (Z_to_bv 64 0x860b4).
(* 0x860b4-0x860c4: the frame, the saved ra and the index; stop at 0x860c8 bltu a1,a0 *)
cw_run ltac:(cw_awr_stk). cw_keep ltac:(cw_kwr_stk).
cw_branch Hb.
- (* taken: 90 < i, the function returns -1 (0x86100-0x8610c) *)
  rewrite branch_ltu_U, (U_lit E 90 ltac:(lia)), (cdc_U_idx E c ltac:(lia) E10) in Hb.
  apply Z.ltb_lt in Hb.
  cw_run ltac:(cw_awr_stk). cw_keep ltac:(cw_kwr_stk).
  cw_leaf ltac:(idtac; cw_kept HJ0 KE ltac:(intros ? []) ltac:(intros ? Hz; left; cbv beta in Hz; unfold T_seg7; lia))
          ltac:(cbv beta; rewrite R10, (seg7_spec_big c Hb), denot_lit_U, U_SLit;
                unfold w64; apply Z_to_bv64_eq_mod; vm_compute; reflexivity).
- (* not taken: i <= 90, the instrumented read of the table word *)
  rewrite branch_ltu_U, (U_lit E 90 ltac:(lia)), (cdc_U_idx E c ltac:(lia) E10) in Hb.
  apply Z.ltb_ge in Hb.
  (* 0x860cc-0x860f0: the shadow offset, a = 0x213a0 + 4 i and its shadow byte; the check's
     obligation is paid by the contract's crd_ok of the whole table *)
  cw_run_ob ltac:(cw_awr_stk)
    ltac:(idtac; lazymatch goal with
          | |- range_addressable (rd_of tfibsegs (mrestrict (w_H ?Wq) ?mq)) _ _ _ =>
            apply (seg7_obl E Wq memc mq c ltac:(lia) E10 E32 Hb HCRDra);
            intros z Hz; unfold CA_SEG7 in Hz;
            assert (Hd : 0 <= z / 8 <= z)
              by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]);
            unfold shadow_of_addr, SHADOW_OFF; apply KE; cbv beta; lia
          end).
  cw_keep ltac:(cw_kwr_stk).
  (* the load at 0x860f8 is at an address the engine cannot split: name it, and give its word the
     region the read-only data holds *)
  lazymatch goal with
  | HS : st_ok tfibsegs ?Ev ?ss (restrict (w_H ?Wq) ?msq) |- _ =>
    assert (E2_10 : ew Ev 10 = Z_to_bv 64 c) by (rewrite !ew_ewset_other by lia; exact E10);
    cw_r10 R10a;
    eapply (st_ok_agree tfibsegs 40%nat Ev
      (ewset (ewset Ev 40 (Z_to_bv 64 (CA_SEG7 + 4 * seg7_idx c))) 41
             (Z_to_bv 64 (seg7_word (seg7_idx c))))) in HS;
    [ | eapply YP03.env_agree_trans;
        [ apply env_agree_ewset
        | eapply YP03.env_agree_le; [ | apply env_agree_ewset ]; lia ]
      | vm_compute; reflexivity ]
  end.
  lazymatch goal with
  | HS : st_ok tfibsegs ?E3 ?ss (restrict (w_H ?Wq) ?msq) |- _ =>
    assert (E3_40 : ew E3 40 = Z_to_bv 64 (CA_SEG7 + 4 * seg7_idx c))
      by (rewrite ew_ewset_other by lia; apply ew_ewset_same);
    assert (E3_41 : ew E3 41 = Z_to_bv 64 (seg7_word (seg7_idx c))) by apply ew_ewset_same;
    assert (B2' : bv_unsigned (ew E3 2) = spZ regs) by (rewrite !ew_ewset_other by lia; exact B2);
    assert (HXv : sv_denot E3 (SOff 40 0) = getr (ms_regs (restrict (w_H Wq) msq)) (10%bv : bv 5))
      by (cbn [ms_regs restrict]; rewrite R10a, sv_denot_SOff0, E3_40, denot_lit_U,
          (cdc_U_x _ c ltac:(lia) E2_10); reflexivity);
    eapply (ast_ok_set_reg_fp tfibsegs E3 ss (restrict (w_H Wq) msq) (10%bv : bv 5) (SOff 40 0)) in HS;
    [ | vm_compute; reflexivity | exact HXv ];
    eapply (ast_ok_add_region tfibsegs E3 _ (restrict (w_H Wq) msq)
             (YP09.mkRegion (Some 40%nat) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SOff 41 0))])) in HS;
    [ | vm_compute; reflexivity
      | cbn [ms_mem restrict];
        apply (seg7_tbl_region_ok E3 Wq (ms_mem msq) (seg7_idx c) ltac:(lia) E3_40 E3_41);
        intros z Hz;
        rewrite (KE z ltac:(unfold CA_SEG7 in *; lia) ltac:(unfold CA_SEG7 in *; lia));
        apply HROMc; exact Hz
      | cbn [ss_mem];
        exact (seg7_tbl_disj E3 (seg7_idx c) (spZ regs) _ ltac:(lia) E3_40 B2' ltac:(lia)) ];
    clear SHOK;
    assert (SHOK : sh_ok tfibsegs CW_Bx [] E3 (mrestrict (w_H Wq) (ms_mem msq))) by constructor
  end.
  (* 0x860f8-0x8610c: the word, the saved ra, the frame and `ret` *)
  cw_run ltac:(cw_awr_stk). clear B2'. cw_keep ltac:(cw_kwr_stk).
  cw_leaf ltac:(idtac; cw_kept HJ0 KE ltac:(intros ? []) ltac:(intros ? Hz; left; cbv beta in Hz; unfold T_seg7; lia))
          ltac:(cbv beta; rewrite R10, (seg7_spec_small c Hb), denot_lit_U, U_SExt; cbv iota beta;
                rewrite (cw_U_atom0 _ 41%nat (seg7_word (seg7_idx c)) E3_41
                           ltac:(unfold seg7_word;
                                 pose proof (Z.mod_pos_bound (nth (Z.to_nat (seg7_idx c)) seg7_table (-1))
                                              (2 ^ 32) ltac:(lia)); lia));
                change (2 ^ Z.of_N 32) with (2 ^ 32);
                rewrite (seg7_word_mod (seg7_idx c)), (seg7_swrap (seg7_idx c) ltac:(lia));
                unfold w64; apply Z_to_bv64_canon).
Qed.
End d.
End b.
