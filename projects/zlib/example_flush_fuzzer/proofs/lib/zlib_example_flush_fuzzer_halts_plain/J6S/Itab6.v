(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run Fs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.World Require Import Src_zlib_example_flush_fuzzer_repro.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain Require Import PropExec CatExec CatSim SeqExec StoreOk Frame Hoare StepTac.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.E1 Require Import SymEx2Expr SymEx2 SymEx2Tac MemRel IKBridge.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel Require Import Prog ZIface InflateState Inftrees ItCovIface InflateInvCov ItableAeq.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.IK Require Import TSet MstepsGrows ZStep ZMem ZArr ZCall ZCallL IGlue.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.IK6 Require Import IDefs ISpecs.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.I6S Require Import Base S_It1 S_It7.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.D6S Require Import Segs6 Callee6 CalleeKits6.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.J6S Require Import InflRod6 InflCtx6 Callee6i.
Import ListNotations.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.PropExec.FPState}.

Definition MD0 : Model := mkModel [] (mkVmMaps [] [] (Z_to_bv 64 0) (Z_to_bv 64 0) 0) IEof [] None None None.
Lemma MD0_halted : m_halted MD0 = None.
Proof using. reflexivity. Qed.

Lemma R_segs_s6 : R_segs = s6_segs.
Proof using. reflexivity. Qed.

Lemma rom_ok_of_rod6 : forall M, rod6_clear M -> rom_ok M.
Proof using.
  intros M H x Hx. unfold ROM_LO, ROM_HI in Hx. unfold rod6_clear, ROD6_LO, ROD6_HI in H. apply H. lia.
Qed.

Lemma rom_it_tabs6 : forall M, rom_ok M ->
  mem_arr 2 R_segs M LBASE_ADDR 31 (arr_get lbase_a) /\ mem_arr 2 R_segs M LEXT_ADDR 31 (arr_get lext_a) /\
  mem_arr 2 R_segs M DBASE_ADDR 32 (arr_get dbase_a) /\ mem_arr 2 R_segs M DEXT_ADDR 32 (arr_get dext_a).
Proof using.
  intros M H. cbv [LBASE_ADDR LEXT_ADDR DBASE_ADDR DEXT_ADDR].
  split; [eapply mem_arr_ext; [apply rom_lbase_arr; exact H | intros; apply lbase_f_model; assumption]|].
  split; [eapply mem_arr_ext; [apply rom_lext_arr; exact H | intros; apply lext_f_model; assumption]|].
  split; [eapply mem_arr_ext; [apply rom_dbase_arr; exact H | intros; apply dbase_f_model; assumption]|].
  eapply mem_arr_ext; [apply rom_dext_arr; exact H | intros; apply dext_f_model; assumption].
Qed.

Lemma cells_extf : forall M P st (w : nat) n (f g : Z -> Z),
  cells s6_segs M P st w n f -> (forall i, 0 <= i < n -> f i = g i) -> cells s6_segs M P st w n g.
Proof using. intros M P st w n f g H E i Hi. rewrite <- (E i Hi). exact (H i Hi). Qed.

Lemma it_keeps_cover :
  forallb (fun r : reg => reg_in r it_clob6 || bv_eqb r 0%bv || reg_in r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv) all_regs = true.
Proof using. vm_compute. reflexivity. Qed.

Lemma land_of_ret_ok : forall ra : word, ret_ok ra -> Z.land (bv_unsigned ra) (-2) = bv_unsigned ra.
Proof using.
  intros ra H. unfold ret_ok, SeqExec.v_jalr, jalr_tgtZ in H. rewrite Z.add_0_r in H.
  apply (f_equal bv_unsigned) in H. rewrite Z_to_bv_unsigned in H.
  pose proof (u64_range ra) as B.
  assert (R0 : 0 <= Z.land (bv_unsigned ra) (-2)) by (apply Z.land_nonneg; lia).
  assert (R : Z.land (bv_unsigned ra) (-2) < 2 ^ 64).
  { apply Z_bounded_by_bits; [lia | exact R0 |].
    intros k Hk. rewrite Z.land_spec, (Z_testbit_high 64 (bv_unsigned ra) k) by lia. reflexivity. }
  rewrite bv_wrap_small in H; [exact H|]. unfold bv_modulus. lia.
Qed.

Theorem itable_run6_ok : itable_run6.
Proof using.
  unfold itable_run6. intros M R ty S lo codes nx bits pb usp ra lens tbl work.
  intros G10 G11 G12 G13 G14 G15 G2 G1 RET Hpb HS0 HS1 HS16 HoS Husp0 Husp1 Husp47 Husp16 HSb MF MS ROD Llen Ltbl Lwork
         Clens Ccodes Cwork Cnx Cpb Blens Btbl Bwork Hlo0 Hloc Hc0 Hl15 HtyC HtyD Hbits Hnx0 Hroom.
  cbv zeta. unfold ITFR6, IMG6_TOP in *. unfold offimg, IMG6_TOP in HoS.
  pose proof (u64_range ra) as Bra.
  set (Rb := zlift R).
  assert (Gk : forall rg : reg, bv_eqb rg 0%bv = false -> zget_l Rb [] (bv_key rg) = bv_unsigned (getr R rg)).
  { intros rg Hr. cbv [zget_l alookup]. subst Rb. rewrite zget_zlift, (getr_reg_get R rg Hr). reflexivity. }
  assert (GZ : forall (rg : reg) k v, bv_eqb rg 0%bv = false -> bv_key rg = k -> getr R rg = zw v -> 0 <= v < 2 ^ 64 -> zget_l Rb [] k = v).
  { intros rg k v Hr <- Hv Bv. rewrite (Gk rg Hr), Hv. apply u_zw_small. exact Bv. }
  assert (LA0 : zget_l Rb [] kA0 = cty ty) by (apply (GZ 10%bv); [reflexivity | reflexivity | rewrite G10; destruct ty; reflexivity | destruct ty; cbn; lia]).
  assert (LA1 : zget_l Rb [] kA1 = S + 168 + 2 * lo) by (apply (GZ 11%bv); [reflexivity | reflexivity | unfold o_lens; exact G11 | unfold o_lens; lia]).
  assert (LA2 : zget_l Rb [] kA2 = codes) by (apply (GZ 12%bv); [reflexivity | reflexivity | exact G12 | lia]).
  assert (LA3 : zget_l Rb [] kA3 = S + 160) by (apply (GZ 13%bv); [reflexivity | reflexivity | unfold o_next; exact G13 | unfold o_next; lia]).
  assert (LA4 : zget_l Rb [] kA4 = pb) by (apply (GZ 14%bv); [reflexivity | reflexivity | exact G14 | lia]).
  assert (LA5 : zget_l Rb [] kA5 = S + 808) by (apply (GZ 15%bv); [reflexivity | reflexivity | unfold o_work; exact G15 | unfold o_work; lia]).
  assert (LSP : zget_l Rb [] kSP = usp) by (apply (GZ 2%bv); [reflexivity | reflexivity | exact G2 | lia]).
  assert (LRA : zget_l Rb [] kRA = bv_unsigned ra) by (change kRA with (bv_key (1%bv : reg)); rewrite (Gk 1%bv eq_refl), G1; reflexivity).
  pose proof (land_of_ret_ok ra RET) as Hret.
  pose proof (rom_ok_of_rod6 M ROD) as ROM. pose proof (rom_it_tabs6 M ROM) as (Tlb & Tle & Tdb & Tde). rewrite R_segs_s6 in Tlb, Tle, Tdb, Tde.
  assert (Wf : mem_wr s6_segs M (usp - 192) 192) by (apply mapped_mem_wr; [lia | lia | exact MF]).
  assert (Wp : mem_wr s6_segs M S STATE_SIZE) by (unfold STATE_SIZE; apply mapped_mem_wr; [lia | lia | exact MS]).
  assert (Alens : mem_arr 2 s6_segs M (S + 168) N_LENS (arr_get lens)) by (unfold o_lens, N_LENS; apply cells_mem_arr; [lia | lia | lia | lia | exact Clens]).
  assert (Acodes : mem_arr 4 s6_segs M (S + 1384) N_CODES (arr_get tbl)) by (unfold o_codes, N_CODES; apply cells_mem_arr; [lia | lia | lia | lia | exact Ccodes]).
  assert (Awork : mem_arr 2 s6_segs M (S + 808) N_WORK (arr_get work)) by (unfold o_work, N_WORK; apply cells_mem_arr; [lia | lia | lia | lia | exact Cwork]).
  assert (Anx : mem_u64 s6_segs M (S + 160) (S + 1384 + 4 * nx)) by (unfold o_next, o_codes; apply (proj2 (mem_u64_cell s6_segs M _ _)); exact Cnx).
  assert (Apb : mem_u32 s6_segs M pb bits) by (apply (proj2 (mem_u32_cell s6_segs M _ _)); exact Cpb).
  set (r := inflate_table ty lens lo codes tbl nx bits work).
  set (r' := inflate_table ty (arr_init N_LENS (arr_get lens)) lo codes (arr_init N_CODES (arr_get tbl)) nx bits (arr_init N_WORK (arr_get work))).
  pose proof (inflate_table_aeq ty lens (arr_init N_LENS (arr_get lens)) lo codes tbl (arr_init N_CODES (arr_get tbl)) nx bits work (arr_init N_WORK (arr_get work))
                (aeq_init_get _ _ Llen) (aeq_init_get _ _ Ltbl) (aeq_init_get _ _ Lwork)) as AQ.
  fold r r' in AQ.
  pose proof (inflate_table_lengths ty lens lo codes tbl nx bits work) as LEN. cbv zeta in LEN. fold r in LEN.
  destruct r as [[[[rv T] tab] b] W] eqn:Er. destruct r' as [[[[rv' T'] tab'] b'] W'] eqn:Er'.
  destruct AQ as (Erv & Etab & Eb & AT & AW). subst rv' tab' b'.
  cbn [fst snd] in LEN. destruct LEN as [LT LW].
  set (Q := fun c : config => exists (R' : tree Z) (M' : word -> option byte) (cf' wf' : Z -> Z),
    c = zcfg s6_segs (bv_unsigned ra) (zupd R' []) M' MD0
    /\ zget R' kA0 = rv /\ (rv = 0 \/ rv = 1 \/ rv = -1)
    /\ (forall i, 0 <= i < N_CODES -> cf' i = arr_get T' i) /\ (forall i, 0 <= i < N_WORK -> wf' i = arr_get W' i)
    /\ (forall i, 0 <= i < N_CODES -> 0 <= cf' i < 4294967296) /\ (forall i, 0 <= i < N_WORK -> 0 <= wf' i < 65536)
    /\ mpostL s6_segs M M' (it_fp14 S pb usp 192)
    /\ mem_arr 2 s6_segs M' (S + 168) N_LENS (arr_get lens) /\ mem_arr 4 s6_segs M' (S + 1384) N_CODES cf' /\ mem_arr 2 s6_segs M' (S + 808) N_WORK wf'
    /\ mem_u64 s6_segs M' (S + 160) (S + 1384 + 4 * tab) /\ mem_u32 s6_segs M' pb b
    /\ kept_eq Rb [] R').
  assert (HR : realizes s6_segs (zcfg s6_segs A_ITABLE (zupd Rb []) M MD0) Q).
  { pose proof itable_s as IT. unfold itable_spec_at14 in IT. rewrite R_segs_s6 in IT.
    eapply (IT Rb [] M MD0 Q ty S lo codes nx bits pb usp (bv_unsigned ra) (usp - 192) (arr_get lens) (arr_get tbl) (arr_get work) MD0_halted
              LA0 LA1 LA2 LA3 LA4 LA5 LSP LRA Hret ltac:(rewrite two64_eq; exact Bra)).
    - exact Hpb.
    - exact HS16.
    - exact HS0.
    - unfold STATE_SIZE. lia.
    - lia.
    - unfold DEXT_ADDR. lia.
    - lia.
    - exact Husp16.
    - unfold ZSEP, STATE_SIZE, ROM_LO_ALL, DEXT_ADDR. lia.
    - exact Wf.
    - exact Wp.
    - exact Alens.
    - exact Acodes.
    - exact Awork.
    - exact Anx.
    - exact Apb.
    - exact Tlb.
    - exact Tle.
    - exact Tdb.
    - exact Tde.
    - unfold N_LENS. exact Blens.
    - unfold N_CODES. exact Btbl.
    - unfold N_WORK. exact Bwork.
    - exact Hlo0.
    - unfold N_LENS. exact Hloc.
    - lia.
    - lia.
    - exact Hl15.
    - exact HtyC.
    - exact HtyD.
    - lia.
    - lia.
    - exact Hnx0.
    - unfold N_CODES. exact Hroom.
    -
      intros R' M' cf' wf'. cbv zeta. fold r'. rewrite Er'. cbn [it_ret it_tbl it_work it_table it_bits fst snd].
      intros Q1 Q2 Q3 Q4 Q5 Q6 Q7 Q8 Q9 Q10 Q11 Q12 Q13.
      apply rz_now. subst Q. cbv beta. exists R', M', cf', wf'. split; [reflexivity|].
      repeat (split; [assumption|]). exact Q13. }
  destruct HR as (ms' & RUN & HQ). subst Q. cbv beta in HQ. cbn [cfg_ms cfg_model zcfg] in RUN, HQ.
  destruct HQ as (R' & M' & cf' & wf' & E & Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & KE).
  unfold zcfg in E. injection E as E1. subst ms'.
  unfold zst in RUN. cbn [zupd] in RUN. subst Rb. rewrite zden_zlift in RUN. rewrite (w64_of_word ra) in RUN.
  change (w64 A_ITABLE) with (zw A6_ITABLE) in RUN. change (seg_rom s6_segs) with s6_rom in RUN.
  exists (zden (zupd R' [])), M'.
  assert (GET : forall (rg : reg) k v, bv_eqb rg 0%bv = false -> bv_key rg = k -> zget R' k = v -> getr (zden (zupd R' [])) rg = zw v).
  { intros rg k v Hr Hk Hv. cbn [zupd]. rewrite (getr_zkey R' rg Hr), Hk, Hv. reflexivity. }
  unfold it_ret, it_tbl, it_work, it_table, it_bits. cbn [fst snd].
  split; [exact RUN|].
  split; [exact (GET 10%bv kA0 rv eq_refl eq_refl Q1)|].
  split; [exact Q2|].
  split.
  { destruct KE as (KSP & _). apply (GET 2%bv kSP usp eq_refl eq_refl). rewrite KSP. exact LSP. }
  split.
  {
    apply (frame_of_keeps [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv it_clob6 R (zden (zupd R' []))); [| exact it_keeps_cover].
    destruct KE as (KSP & KGP & KTP & K0 & K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11).
    assert (KEEP : forall (r0 : reg) k, bv_eqb r0 0%bv = false -> bv_key r0 = k -> zget R' k = zget_l (zlift R) [] k -> getr (zden (zupd R' [])) r0 = getr R r0).
    { intros r0 k Hr0 Hk HQk. cbn [zupd]. rewrite (getr_zkey R' r0 Hr0), Hk, HQk, <- Hk, (Gk r0 Hr0). apply w64_of_word. }
    intros r0 Hr0. cbn [In] in Hr0.
    repeat (destruct Hr0 as [<- | Hr0];
      [ eapply KEEP; [ reflexivity | reflexivity
                     | first [ exact KSP | exact KGP | exact KTP | exact K0 | exact K1 | exact K2 | exact K3 | exact K4 | exact K5
                             | exact K6 | exact K7 | exact K8 | exact K9 | exact K10 | exact K11 ] ] |]).
    destruct Hr0. }
  split; [unfold o_lens, N_LENS in Q8; exact (mem_arr_cells s6_segs 2 M' _ _ _ Q8)|].
  split.
  { unfold o_codes, N_CODES in Q9. apply (cells_extf M' _ _ _ _ cf'); [exact (mem_arr_cells s6_segs 4 M' _ _ _ Q9)|].
    intros i Hi. rewrite (Q3 i Hi). symmetry. apply (proj2 AT). }
  split.
  { unfold o_work, N_WORK in Q10. apply (cells_extf M' _ _ _ _ wf'); [exact (mem_arr_cells s6_segs 2 M' _ _ _ Q10)|].
    intros i Hi. rewrite (Q4 i Hi). symmetry. apply (proj2 AW). }
  split; [unfold o_next, o_codes in Q11; exact (proj1 (mem_u64_cell s6_segs M' _ _) Q11)|].
  split; [exact (proj1 (mem_u32_cell s6_segs M' _ _) Q12)|].
  split; [rewrite LT; exact Ltbl|]. split; [rewrite LW; exact Lwork|].
  split; [intros i Hi; rewrite (proj2 AT), <- (Q3 i Hi); apply Q5; exact Hi|].
  split; [intros i Hi; rewrite (proj2 AW), <- (Q4 i Hi); apply Q6; exact Hi|].
  split.
  {
    intros R0.
    pose proof (tab_ok_of_shape ty lens lo codes tbl nx bits work ltac:(lia)
                  ltac:(intros i Hi; split; [pose proof (Blens (lo + i) ltac:(lia)); lia | apply Hl15; exact Hi])
                  HtyC HtyD Hbits Hnx0 ltac:(rewrite Ltbl; exact Hroom) ltac:(rewrite Lwork; lia)) as TS.
    cbv zeta in TS. fold (inflate_table ty lens lo codes tbl nx bits work) in TS.
    replace (inflate_table ty lens lo codes tbl nx bits work) with (rv, T, tab, b, W) in TS by (symmetry; exact Er).
    cbn [fst snd] in TS. destruct (TS R0) as (_ & B1 & T1 & _ & _).
    split; [exact B1|]. assert (2 <= 2 ^ b) by (change 2 with (2 ^ 1) at 1; apply Z.pow_le_mono_r; lia). lia. }
  split; [pose proof (msteps_mem_grows s6_segs _ _ RUN) as G; cbn [ms_mem] in G; exact G|].
  intros x N1 N2 N3 N4. destruct Q7 as [AG _]. apply AG. unfold it_fp14, o_next, o_work, o_codes, N_WORK, N_CODES. cbn [outside_all].
  repeat split; lia.
Qed.
End FXG.
