(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.skcms.iccprofile_info.images Require Ubsan.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require PropExec CatExec CatSim SeqExec StoreOk SymExec Hoare Frame PropExecFP.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require SymExecFP SymExecFPSound SymRunFP SymDriveFP SymCallFP LibDefs LibFrame LibFPLib LibRodata.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require PerfKc.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require LibTagsSpec LibWP1Spec FuzzContract.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require SymDriveLZ.
Unset Nia Cache.  (* [comment removed for export] *)

Module LibFuzzUbA.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.skcms.iccprofile_info.images.Ubsan.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PropExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SeqExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.StoreOk OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Hoare OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Frame OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PropExecFP.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExecFP OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExecFPSound OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymRunFP OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDriveFP OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymCallFP OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibDefs OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibFrame OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibFPLib OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibRodata.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PerfKc.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibTagsSpec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibWP1Spec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.FuzzContract.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDriveLZ.
(* [comment removed for export] *)
#[local] Ltac SymDriveFP.ev_simpl E ::= ev_simpl_lz E.
#[local] Ltac SymDriveFP.ev_simpl_in E H ::= ev_simpl_in_lz E H.
(* [comment removed for export] *)
#[local] Ltac SymDriveFP.run_fp_with_h HR HF HK fuel stops scr chints keep extra ::= run_fp_with_h_lz HR HF HK fuel stops scr chints keep extra.
#[local] Ltac SymDriveFP.branch_case_with HR HF HK Hc ::= branch_case_with_lz HR HF HK Hc.
Unset Lia Cache.
Import ListNotations.
Open Scope bv_scope.
Import SXF. Import SXFS.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

#[local] Abbreviation SEGS := Ubsan.M.loaded_segments.

(* [comment removed for export] *)
Ltac in_lit := cbn; repeat (first [left; reflexivity | right]).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma addw_small : forall (x : word) (k s : Z),
  bv_unsigned x = s -> (0 <= s < 2^32)%Z -> (0 <= s + k < 2^31)%Z -> (-2^31 <= k <= 0)%Z ->
  sext 64 (alu32 ALU_ADD (low32 x) (low32 (Z_to_bv 64 k))) = Z_to_bv 64 (s + k).
Proof.
  intros x k s Hx Hs Hsk Hk. apply bv_eq. rewrite sext32_unsigned, Z_to_bv_unsigned.
  change (alu32 ALU_ADD (low32 x) (low32 (Z_to_bv 64 k))) with (low32 x + low32 (Z_to_bv 64 k))%bv.
  rewrite bv_add_unsigned, !low32_unsigned, !Z_to_bv_unsigned, Hx.
  unfold bv_swrap. rewrite !bv_wrap32_mod, !bv_wrap64_mod.
  change (bv_half_modulus 32) with (2^31)%Z. nia.
Qed.

Lemma curves_pick : forall segs M data len p off,
  curves_ok segs M data len p -> In off profile_curve_offsets -> curve_ok segs M data len (p + off).
Proof.
  intros segs M data len p off HC Hin. unfold curves_ok in HC. rewrite Forall_forall in HC. exact (HC off Hin).
Qed.

Lemma parsed_ok_frame : forall segs M M' rs data len bs p,
  frame_mod M M' rs -> parsed_ok segs M data len bs p -> (0 <= p)%Z -> (p + 976 <= 2 ^ 64)%Z -> apart p 976 rs ->
  parsed_ok segs M' data len bs p.
Proof.
  intros segs M M' rs data len bs p Hf (psz & tc & htrc & hasA2B & H0 & H8 & H20 & Ht & Hc & H964 & Hh & H966 & Ha & Hg) Hp0 Hp Hap.
  exists psz, tc, htrc, hasA2B.
  split; [eapply cell64_frame; [exact Hf|exact H0|lia|lia|]; eapply apart_sub; [exact Hap|lia|lia|lia]|].
  split; [eapply cell32_frame; [exact Hf|exact H8|lia|lia|]; eapply apart_sub; [exact Hap|lia|lia|lia]|].
  split; [eapply cell32_frame; [exact Hf|exact H20|lia|lia|]; eapply apart_sub; [exact Hap|lia|lia|lia]|].
  split; [exact Ht|].
  split; [eapply curves_ok_frame; [exact Hf|exact Hc|lia|lia|exact Hap]|].
  split; [eapply cell8_frame; [exact Hf|exact H964|lia|lia|]; eapply apart_sub; [exact Hap|lia|lia|lia]|].
  split; [exact Hh|].
  split; [eapply cell8_frame; [exact Hf|exact H966|lia|lia|]; eapply apart_sub; [exact Hap|lia|lia|lia]|].
  split; [exact Ha|].
  intros Hnz. eapply grid_ok_A2B_frame; [exact Hf|exact (Hg Hnz)|lia|lia|exact Hap].
Qed.

(* [comment removed for export] *)
Lemma outidx_range : forall (w : word), (1824 <= bv_unsigned w < 2 ^ 47)%Z ->
  (4 <= bv_unsigned (alu64 ALU_SRL (alu64 ALU_ADD (mul_div M_MUL (Z_to_bv 64 (-1)) w) (Z_to_bv 64 576)) (Z_to_bv 64 5)) <= 2 ^ 59)%Z.
Proof.
  intros w Hw. rewrite alu_srl, alu_add, m_mul. unfold v_srl, v_add, v_mul.
  rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. rewrite Z.shiftr_div_pow2 by lia.
  change ((-1) mod 2 ^ 64)%Z with (2 ^ 64 - 1)%Z. change ((5 mod 2 ^ 64) mod 64)%Z with 5%Z. change (2 ^ 5)%Z with 32%Z.
  lia.
Qed.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* [comment removed for export] *)
Ltac mlia := intros;
  lazymatch goal with
  | |- context [Z.modulo _ _] => Z.to_euclidean_division_equations; lia
  | |- _ => lia
  end.

Section Proof.
  Hypothesis Hparse : parse_contract SEGS tags_infoub.
  Hypothesis Hgetidx : getidx_contract SEGS tags_infoub.
  Hypothesis Hrte : rte_contract SEGS 0x131b8.

  Variables (FPI : FPState) (regs : bvmap 5 word) (mem rom : word -> option byte).
  Variables (ret sp data : word) (n : Z) (bs : list byte).

  Hypothesis Hra : getr regs 1 = ret.
  Hypothesis Hret : ret_ok ret.
  Hypothesis Hsp : getr regs 2 = sp.
  Hypothesis Ha0 : getr regs 10 = data.
  Hypothesis Ha1 : getr regs 11 = Z_to_bv 64 n.
  Hypothesis Hn : (0 <= n < 2 ^ 26)%Z.
  Hypothesis Hbs : Z.of_nat (length bs) = n.
  Hypothesis Hal : (bv_unsigned sp mod 16 = 0)%Z.
  Hypothesis Hsplo : (1824 <= bv_unsigned sp)%Z.
  Hypothesis Hsphi : (bv_unsigned sp < 2 ^ 47)%Z.
  Hypothesis Hd0 : (0 < bv_unsigned data)%Z.
  Hypothesis Hdhi : (bv_unsigned data + n < 2 ^ 47)%Z.
  Hypothesis Hblob : forall i, (0 <= i < n)%Z ->
      mem (Z_to_bv 64 (bv_unsigned data + i)) = Some (nth (Z.to_nat i) bs (Z_to_bv 8 0)).
  Hypothesis Hstk : store_ok SEGS mem (Z_to_bv 64 (bv_unsigned sp - 1824)) (Z.to_nat 1824) = true.
  Hypothesis Hgfw : store_ok SEGS mem (Z_to_bv 64 0x31400) 4 = true.
  Hypothesis Hgfr : exists gb, rdn SEGS mem (Z_to_bv 64 0x31400) 4 = Some gb.
  Hypothesis Hro : forall i, (0x103ec <= i < 0x10490)%Z -> mem (Z_to_bv 64 i) = None.
  Hypothesis Hdj1 : (bv_unsigned data + n <= bv_unsigned sp - 1824 \/ bv_unsigned sp <= bv_unsigned data)%Z.
  Hypothesis Hdj2 : (bv_unsigned data + n <= 0x31400 \/ 0x31400 + 4 <= bv_unsigned data)%Z.
  Hypothesis Hdj3 : (0x31400 + 4 <= bv_unsigned sp - 1824 \/ bv_unsigned sp <= 0x31400)%Z.

  (* [comment removed for export] *)
  Ltac touch := pose proof (Hparse, Hgetidx, Hrte, @fp_regs FPI, regs, mem, rom, ret, sp, data, n, bs, Hra, Hret, Hsp, Ha0, Ha1,
                            Hn, Hbs, Hal, Hsplo, Hsphi, Hd0, Hdhi, Hblob, Hstk, Hgfw, Hgfr, Hro, Hdj1, Hdj2, Hdj3) as HALL;
                clear HALL.

  #[local] Abbreviation s := (bv_unsigned sp).
  #[local] Abbreviation BIG := [(Z_to_bv 64 (s - 1824), 1824%Z); (Z_to_bv 64 0x31400, 4%Z)].

  (* [comment removed for export] *)
  Definition Q (st' : machine_state) : Prop :=
    exists (FPI' : FPState) regs' mem', st' = mkst (FP:=FPI') regs' ret mem' rom /\
      getr regs' 10 = Z_to_bv 64 0 /\
      (forall r, In r fuzz_kept -> getr regs' r = getr regs r) /\
      frame_mod mem mem' BIG.

  (* [comment removed for export] *)
  Definition MEMB (M : word -> option byte) : Prop :=
    cell64 SEGS M (s - 8) ret /\ cell64 SEGS M (s - 16) (getr regs 8) /\ cell64 SEGS M (s - 24) (getr regs 9) /\
    cell64 SEGS M (s - 32) (getr regs 18) /\ cell64 SEGS M (s - 40) (getr regs 19) /\
    frame_mod mem M BIG /\ writable SEGS M (s - 1824) 1824 /\ writable SEGS M 0x31400 4 /\
    (exists gw, cell SEGS M 0x31400 4 gw) /\ rodata_clear M 0x103ec 0x10490 /\ data_ok M data n bs.

  Definition BASE (R : bvmap 5 word) (M : word -> option byte) : Prop :=
    getr R 2 = Z_to_bv 64 (s - 1056) /\
    (forall r, In r [3; 4; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr R r = getr regs r) /\
    MEMB M.

  (* [comment removed for export] *)
  Lemma data_ok0 : data_ok mem data n bs.
  Proof. split; [exact Hn|]. split; [exact Hbs|]. split; [exact Hd0|]. split; [exact Hdhi|]. exact Hblob. Qed.

  Lemma writable0 : writable SEGS mem (s - 1824) 1824.
  Proof. pose proof (u64_range sp). split; [lia|]. split; [lia|]. split; [lia|]. exact Hstk. Qed.

  Lemma gfool0 : writable SEGS mem 0x31400 4 /\ exists gw, cell SEGS mem 0x31400 4 gw.
  Proof.
    split; [split; [lia|]; split; [lia|]; split; [lia|]; exact Hgfw|].
    destruct Hgfr as [gb Hgb]. exact (cell_of_rdn SEGS mem 0x31400 4 gb Hgb ltac:(lia)).
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma memb_frame_gf : forall M M', MEMB M -> frame_mod M M' [(Z_to_bv 64 0x31400, 4%Z)] ->
    (exists gw, cell SEGS M' 0x31400 4 gw) -> MEMB M'.
  Proof.
    touch.
    intros M M' (M1 & M2 & M3 & M4 & M5 & Mfr & Mw & Mg & _ & Mro & Md) Hf Hgw.
    pose proof (u64_range sp). pose proof (u64_range data). pose proof Hn. clear Hdj1.
    unfold MEMB.
    repeat match goal with
    | |- cell64 _ _ _ _ /\ _ => split; [eapply cell64_frame; [exact Hf | eassumption | lia | lia | solve_apart]|]
    end.
    split; [eapply frame_mod_trans_same; [exact Mfr|]; eapply frame_mod_in2r; [| |exact Hf]; rewrite ?u_small by lia; lia|].
    split; [eapply writable_frame; [exact Hf | exact Mw]|].
    split; [eapply writable_frame; [exact Hf | exact Mg]|].
    split; [exact Hgw|].
    split; [eapply rodata_clear_frame; [exact Hf | exact Mro | lia | lia | solve_apart]|].
    eapply data_ok_frame; [exact Hf | exact Md | solve_apart].
  Qed.

  (* [comment removed for export] *)
  Lemma memb_frame_in : forall M M' rs, MEMB M -> frame_mod M M' rs ->
    Forall (fun r => s - 1824 <= bv_unsigned (fst r) /\ bv_unsigned (fst r) + snd r <= s - 40)%Z rs -> MEMB M'.
  Proof.
    touch.
    intros M M' rs (M1 & M2 & M3 & M4 & M5 & Mfr & Mw & Mg & Mc & Mro & Md) Hf Hrs.
    pose proof (u64_range sp). pose proof (u64_range data). pose proof Hn.
    pose proof (writable_rodata_apart_Ub M _ _ 0x103ec 0x10490 ltac:(lia) ltac:(lia) ltac:(lia) Mw Mro) as Hsro.
    assert (Hap : forall lo k, (s - 40 <= lo \/ lo + k <= s - 1824)%Z -> apart lo k rs).
    { intros lo k Hlo. unfold apart. eapply Forall_impl; [|exact Hrs]. intros [b m] Hb. cbn [fst snd] in *. lia. }
    unfold MEMB.
    repeat match goal with
    | |- cell64 _ _ _ _ /\ _ => split; [eapply cell64_frame; [exact Hf | eassumption | lia | lia | apply Hap; lia]|]
    end.
    split.
    { eapply frame_mod_trans_same; [exact Mfr|]. apply (frame_mod_incl _ _ rs); [|exact Hf].
      intros b m Hin. exists (Z_to_bv 64 (s - 1824)), 1824%Z. split; [left; reflexivity|].
      rewrite Forall_forall in Hrs. specialize (Hrs _ Hin). cbn [fst snd] in Hrs. rewrite u_small by lia. lia. }
    split; [eapply writable_frame; [exact Hf | exact Mw]|].
    split; [eapply writable_frame; [exact Hf | exact Mg]|].
    split; [destruct Mc as [gw Hgw]; exists gw; eapply cell_frame; [exact Hf | exact Hgw | lia | cbn; lia | apply Hap; lia]|].
    split; [eapply rodata_clear_frame; [exact Hf | exact Mro | lia | lia | apply Hap; lia]|].
    eapply data_ok_frame; [exact Hf | exact Md | apply Hap; lia].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[local] Abbreviation VALS R FR extra := (junk_vals R ++ fjunk_vals FR ++ junk_vals regs ++ Z_to_bv 64 n :: extra).

  (* [comment removed for export] *)
  Definition SRB : list expr :=
    sr_upds (sr_vars 0)
      [(2, EAlu ALU_ADD (EVar 66) (ELit (-1056))); (3, EVar 67); (4, EVar 68); (20, EVar 84);
       (21, EVar 85); (22, EVar 86); (23, EVar 87); (24, EVar 88); (25, EVar 89); (26, EVar 90); (27, EVar 91)]%bv.

  Definition KNB : list kentry :=
    [KAlign (EVar 66) 16; KRange (EVar 66) 1824 140737488355328; KRange (EVar 74) 1 140737488355328; KRange (EVar 96) 0 67108864;
     KWord (SA (EVar 66) (-8)) 8 (EVar 65); KWord (SA (EVar 66) (-16)) 8 (EVar 72);
     KWord (SA (EVar 66) (-24)) 8 (EVar 73); KWord (SA (EVar 66) (-32)) 8 (EVar 82);
     KWord (SA (EVar 66) (-40)) 8 (EVar 83);
     KWord (SA (ELit 0) 0x31400) 4 (EVar 97);
     KWr (SA (EVar 66) (-1824)) 1824; KWr (SA (ELit 0) 0x31400) 4;
     KDisj (SA (EVar 66) (-1824)) 1824 (SA (ELit 0) 0x31400) 4].
  (* [comment removed for export] *)
  Definition KND : list kentry := [KBlobD (SA (EVar 74) 0) (EVar 96) 0].

  Lemma packB : forall (R : bvmap 5 word) (FR : bvmap 5 word) (M : word -> option byte) (gw : word) (extra : list word),
    BASE R M -> cell SEGS M 0x31400 4 gw ->
    let E := Env (vals_ev (VALS R FR (gw :: extra))) (blobs_ev [bs]) in
    regs_ok E SRB R /\ fregs_ok E (sfr_vars 32) FR /\ know_ok SEGS E M KNB /\ know_ok SEGS E M KND /\
    regs_ok E (sr_vars 64) regs.
  Proof.
    touch.
    intros R FR M gw extra (R2 & RK & (M1 & M2 & M3 & M4 & M5 & Mfr & Mw & Mg & Mc & Mro & Md)) Hgw E.
    pose proof (u64_range sp) as Hspr. pose proof Mw as (W1 & W2 & W3 & W4). pose proof Mg as (G1 & G2 & G3 & G4).
    pose proof Md as (D1 & D2 & D3 & D4 & D5).
    clear Hdj1 Hdj2 Mfr.
    unfold cell64, cell in *.
    split; [|split; [|split; [|split]]].
    - unfold SRB. apply regs_ok_pins; [exact (regs_ok_vars [] R _ (blobs_ev [bs]))|].
      repeat (apply Forall_cons; [cbn [fst snd edenot]; ev_simpl E; rewrite_getr; rewrite ?alu_add_lit;
                                  first [ reflexivity | apply RK; in_lit | f_equal; lia ] |]).
      apply Forall_nil.
    - exact (fregs_ok_vars (junk_vals R) FR _ (blobs_ev [bs])).
    - unfold KNB.
      constructor; [apply kalign_intro; [lia | cbn [edenot]; ev_simpl E; rewrite Hsp; exact Hal]|].
      constructor; [apply krange_intro; cbn [edenot]; ev_simpl E; rewrite Hsp; lia|].
      constructor; [apply krange_intro; cbn [edenot]; ev_simpl E; rewrite Ha0; lia|].
      constructor; [apply krange_intro; cbn [edenot]; ev_simpl E; rewrite u_small by lia; lia|].
      Ltac kw E0 H := eapply (kword_intro SEGS _ _ (EVar 66) sp _ _ _ _);
                      [cbn [edenot]; ev_simpl E0; assumption | cbn [edenot]; ev_simpl E0; reflexivity | lia | lia | lia | lia |
                       lazymatch goal with |- rdn _ _ (Z_to_bv 64 ?a) _ = _ =>
                         lazymatch type of H with rdn _ _ (Z_to_bv 64 ?b) _ = _ => replace a with b by lia; rewrite_getr; exact H end end].
      constructor; [kw E M1|]. constructor; [kw E M2|]. constructor; [kw E M3|].
      constructor; [kw E M4|]. constructor; [kw E M5|].
      constructor; [eapply (kword_intro SEGS E M (ELit 0) (Z_to_bv 64 0) 0x31400 4 (EVar 97) gw);
                    [reflexivity | cbn [edenot]; ev_simpl E; reflexivity | lia | lia
                    | rewrite u_small by lia; lia | rewrite u_small by lia; cbn; lia
                    | rewrite u_small by lia; exact Hgw]|].
      constructor; [apply (kwr_intro SEGS E M (EVar 66) sp (-1824) 1824);
                    [cbn [edenot]; ev_simpl E; exact Hsp | lia | lia | lia |
                     replace (bv_unsigned sp + -1824)%Z with (bv_unsigned sp - 1824)%Z by lia; exact W4]|].
      constructor; [apply (kwr_intro SEGS E M (ELit 0) (Z_to_bv 64 0) 0x31400 4 eq_refl);
                    rewrite ?u_small by lia; cbn [Z.add]; try lia; exact G4|].
      constructor; [cbn [kentry_ok]; unfold estart; cbn [a_base a_off edenot]; ev_simpl E; rewrite Hsp; rewrite u_small by lia; lia|].
      constructor.
    - unfold KND. constructor; [|constructor].
      cbn [kentry_ok]. unfold flat, estart, elenZ. cbn [a_base a_off edenot]. ev_simpl E.
      rewrite Ha0. rewrite u_small by lia. split; [lia|]. split; [exact D2|].
      intros i Hi. rewrite Z.add_0_r. apply D5. exact Hi.
    - exact (regs_ok_vars (junk_vals R ++ fjunk_vals FR) regs (Z_to_bv 64 n :: gw :: extra) (blobs_ev [bs])).
  Qed.

  Ltac rewrite_getr_in H :=
    repeat match goal with G : getr ?R ?r = _ |- _ => rewrite G in H end.

  (* [comment removed for export] *)
  Ltac kcell HK b k n v H :=
    lazymatch type of HK with know_ok _ ?E0 ?M0 ?kn =>
      let KR := fresh "KR" in let Hfl := fresh "Hfl" in
      kread_rdn_fast SEGS E0 M0 kn b k n v HK H;
      lazymatch type of H with ?FL -> _ =>
        assert (Hfl : FL) by (unfold flat, estart; cbn [a_base a_off edenot]; ev_simpl E0; rewrite_getr; rewrite ?u_small by lia; lia);
        specialize (H Hfl); clear Hfl end;
      unfold adenot, v_addi in H; cbn [a_base a_off edenot] in H; ev_simpl_in E0 H; rewrite_getr_in H
    end.
  Ltac kcell_auto HK b k n H :=
    lazymatch type of HK with know_ok _ _ _ ?kn =>
      let r := eval vm_compute in (kread SEGS kn b k n) in
      lazymatch r with Some ?v => kcell HK b k n v H end end.

  Ltac frame_of_log RS fixup :=
    lazymatch goal with
    | |- frame_mod ?M0 (mem_denot ?E0 ?M0 ?log) ?regions =>
        replace regions with (regions_denot E0 RS)
          by (cbn [regions_denot map fst snd]; unfold adenot; cbn [a_base a_off edenot]; ev_simpl E0; fixup; reflexivity);
        apply (frame_mod_mem_denot E0 M0 log RS);
          [ lazymatch goal with H : log_flat _ log |- _ => exact H end
          | repeat (apply Forall_cons); [..|apply Forall_nil]; cbn [fst snd]; unfold flat, estart; cbn [a_base a_off edenot]; ev_simpl E0; fixup; lia
          | vm_compute; reflexivity ]
    end.

  Ltac subst_triv := repeat match goal with H : ?a = ?b |- _ => is_var a; is_var b; subst a end.

  Ltac solve_reg := rewrite_getr; rewrite ?alu_add_lit; rewrite ?u_small by lia;
                    rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; first [reflexivity | f_equal; lia | idtac].
  Ltac creg r := lazymatch goal with HR : regs_ok _ _ ?R' |- getr ?R' _ = _ => regv HR r; solve_reg end.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma phaseE : forall (FPX : FPState) R M, BASE R M ->
    runs_to SEGS (mkst (FP:=FPX) R (Z_to_bv 64 0x13194) M rom) Q.
  Proof.
    touch.
    intros FPX R M HB. pose proof HB as (R2 & RK & HMB).
    pose proof HMB as (_ & _ & _ & _ & _ & Mfr & _ & _ & Mc & _).
    destruct Mc as [gw Hgw].
    pose proof (u64_range sp) as Hspr.
    destruct (packB R (fp_regs (FPState:=FPX)) M gw [] HB Hgw) as (HR & HF & HK & _ & H64).
    pose proof (H64 : id _) as H64i. clear H64.
    run_fp 100%nat (@nil Z) noscr false.
    fin_ret.
    unfold Q.
    lazymatch goal with |- exists _ _ _, @mkst ?I ?R' _ ?M' _ = _ /\ _ => exists I, R', M' end.
    split; [regv HR (1%bv:reg); rewrite_getr; reflexivity|].
    split; [regv HR (10%bv:reg); reflexivity|].
    split; [| exact Mfr].
    lift_id H64i HR.
    exact (regs_same_on _ _ _ regs _ fuzz_kept H64i HR ltac:(vm_compute; reflexivity)).
  Qed.

  (* [comment removed for export] *)
  Ltac call_rte_auto HC :=
    lazymatch goal with |- runs_to _ (@mkst ?I ?R' _ ?M' _) _ =>
    lazymatch goal with HR : regs_ok _ ?sr R' |- _ =>
      lazymatch eval vm_compute in (sr_get sr 10%bv) with
      | EAlu ALU_ADD (EVar 66) (ELit ?k) =>
        let OFF := eval vm_compute in (k + 1016)%Z in
        eapply rt_call;
        [ eapply (Hrte data n bs (Z_to_bv 64 (s - 1016 + OFF)) I R' M' rom _);
          [ regv HR (1%bv:reg); reflexivity
          | apply ret_ok_even; rewrite u_small by lia; reflexivity
          | unfold rte_pre;
            split; [regv HR (10%bv:reg); rewrite_getr; rewrite ?alu_add_lit; f_equal; lia|];
            split; [assumption|];
            split; [rewrite u_small by lia; apply (curves_pick _ _ _ _ _ _ HC); in_lit|];
            split; rewrite u_small by lia; mlia ]
        | cbv beta;
          let FPI' := fresh "FPI" in let regs' := fresh "R" in let mem' := fresh "MC" in
          let Hkeep := fresh "Hkeep" in let Hfkeep := fresh "Hfkeep" in let Hmem := fresh "Hmem" in
          intros FPI' regs' mem' (Hkeep & Hfkeep & Hmem); unfold rte_post in Hmem; subst mem';
          unfold regs_kept in Hkeep; clear Hfkeep;
          after_call Hkeep FPI'; clear Hkeep ]
      end end end.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma phaseC : forall (FPX : FPState) R M, BASE R M ->
    getr R 10 = Z_to_bv 64 3 ->
    parsed_ok SEGS M data n bs (s - 1016) ->
    cell SEGS M (s - 1016 + 160 + 300) 4 (Z_to_bv 64 3) ->
    runs_to SEGS (mkst (FP:=FPX) R (Z_to_bv 64 0x1311c) M rom) Q.
  Proof.
    touch.
    intros FPX R M HB R10 HP Hoc. pose proof HB as (R2 & RK & HMB).
    pose proof HMB as (_ & _ & _ & _ & _ & Mfr & Mw & Mg & Mc & Mro & Md).
    destruct Mc as [gw Hgw].
    pose proof HP as (psz & tc & htrc & hasA2B & _ & _ & _ & _ & HC & _).
    pose proof (u64_range sp) as Hspr.
    destruct (packB R (fp_regs (FPState:=FPX)) M gw [] HB Hgw) as (HR & HF & HKB & _ & H64).
    pose proof (H64 : id _) as H64i. clear H64.
    apply (regs_ok_pin _ _ R 10 (ELit 3)) in HR; [| exact R10].
    unfold cell in Hoc.
    lazymatch type of HR with regs_ok ?E _ _ =>
      assert (HK : know_ok SEGS E M (KWord (SA (EVar 66) (-556)) 4 (ELit 3) :: KNB));
      [ constructor; [| exact HKB];
        eapply (kword_intro SEGS E M (EVar 66) sp (-556) 4 (ELit 3) (Z_to_bv 64 3));
          [cbn [edenot]; ev_simpl E; exact Hsp | reflexivity | lia | lia | lia | lia |
           replace (bv_unsigned sp + -556)%Z with (s - 1016 + 160 + 300)%Z by lia; exact Hoc]
      | clear HKB ] end.
    (* [comment removed for export] *)
    lazymatch type of HK with know_ok ?segs ?E ?M0 ?kn =>
      let H := fresh "HK" in
      assert (H : know_ok segs E M0 (KRange (EAlu ALU_SRL (EAlu ALU_ADD (EMd M_MUL (ELit (-1)) (EVar 66)) (ELit 576)) (ELit 5)) 4 576460752303423488 :: kn));
      [ apply know_ok_cons; [apply krange_intro; cbn [edenot]; ev_simpl E; rewrite_getr; apply outidx_range; lia | exact HK]
      | clear HK; rename H into HK ] end.
    run_fp 100%nat [0x131b8%Z] noscr false. call_rte_auto HC.
    run_fp 100%nat [0x131b8%Z] noscr false. call_rte_auto HC.
    run_fp 100%nat [0x131b8%Z] noscr false. call_rte_auto HC.
    run_fp 100%nat [0x131b8%Z] noscr false. call_rte_auto HC.
    run_fp 100%nat [0x131b8%Z] noscr false. call_rte_auto HC.
    run_fp 100%nat [0x131b8%Z] noscr false. call_rte_auto HC.
    run_fp 100%nat [0x13194%Z] noscr true.
    apply phaseE.
    split; [creg (2%bv:reg)|].
    split; [lift_id H64i HR;
            lazymatch type of HR with regs_ok ?E ?sr _ =>
            lazymatch type of H64i with id (regs_ok _ ?sr0 _) =>
              exact (regs_same_on E sr0 sr regs _ [3; 4; 20; 21; 22; 23; 24; 25; 26; 27]%bv H64i HR ltac:(vm_compute; reflexivity)) end end|].
    eapply (memb_frame_gf M); [exact HMB | rewrite EQM; frame_of_log [(SA (ELit 0) 0x31400, 4%Z)] ltac:(change (bv_unsigned (Z_to_bv 64 0) + 0x31400)%Z with 0x31400%Z) |].
    kcell_auto HK (ELit 0) 0x31400%Z 4%nat HG. rewrite u_small in HG by lia. eexists; exact HG.
  Qed.

  (* [comment removed for export] *)
  Ltac base_same H64i :=
    lazymatch goal with |- BASE ?R' ?M' =>
    lazymatch goal with HR : regs_ok ?E ?sr R', HMB : MEMB M' |- _ =>
      split; [creg (2%bv:reg)|];
      split; [lift_id H64i HR;
              lazymatch type of H64i with id (regs_ok _ ?sr0 _) =>
                exact (regs_same_on E sr0 sr regs R' [3; 4; 20; 21; 22; 23; 24; 25; 26; 27]%bv H64i HR ltac:(vm_compute; reflexivity)) end
             | exact HMB ]
    end end.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma phaseB2 : forall (FPX : FPState) R M (g8 g16 : word) (G : Z), BASE R M ->
    getr R 10 = Z_to_bv 64 3 -> getr R 11 = Z_to_bv 64 G ->
    parsed_ok SEGS M data n bs (s - 1016) ->
    cell SEGS M (s - 1016 + 160 + 300) 4 (Z_to_bv 64 3) ->
    cell64 SEGS M (s - 1016 + 160 + 128) g8 -> cell64 SEGS M (s - 1016 + 160 + 136) g16 ->
    (bv_unsigned g8 <> 0%Z -> inDATA data n (bv_unsigned g8) G) ->
    (bv_unsigned g16 <> 0%Z -> inDATA data n (bv_unsigned g16) (2 * G)) ->
    (1 <= G <= 12684751875)%Z ->
    runs_to SEGS (mkst (FP:=FPX) R (Z_to_bv 64 0x130bc) M rom) Q.
  Proof.
    touch.
    intros FPX R M g8 g16 G HB R10 R11 HP Hoc Hg8 Hg16 Hin8 Hin16 HG. pose proof HB as (R2 & RK & HMB).
    pose proof HMB as (_ & _ & _ & _ & _ & Mfr & Mw & Mg & Mc & Mro & Md).
    destruct Mc as [gw Hgw].
    pose proof (u64_range sp) as Hspr. pose proof (u64_range g8) as Hg8r. pose proof (u64_range g16) as Hg16r.
    pose proof (u64_range data) as Hdr.
    destruct (packB R (fp_regs (FPState:=FPX)) M gw [g8; g16; Z_to_bv 64 G] HB Hgw) as (HR & HF & HKB & HKD & H64).
    pose proof (H64 : id _) as H64i. clear H64.
    apply (regs_ok_pin _ _ R 10 (ELit 3)) in HR; [| exact R10].
    apply (regs_ok_pin _ _ R 11 (EVar 100)) in HR; [| cbn [edenot ev eb vals_ev blobs_ev nth app junk_vals fjunk_vals]; exact R11].
    unfold cell64, cell in Hg8, Hg16.
    lazymatch type of HR with regs_ok ?E _ _ =>
    assert (HK : know_ok SEGS E M
      ((if Z.eq_dec (bv_unsigned g8) 0 then KRange (EVar 98) 0 0 else KRange (EVar 98) 1 140737488355328) ::
       (if Z.eq_dec (bv_unsigned g16) 0 then KRange (EVar 99) 0 0 else KRange (EVar 99) 1 140737488355328) ::
       KWord (SA (EVar 66) (-728)) 8 (EVar 98) :: KWord (SA (EVar 66) (-720)) 8 (EVar 99) ::
       KRange (EVar 100) 1 12684751875 :: KNB ++ KND));
    [ constructor; [pose proof (u64_range g8); destruct (Z.eq_dec _ 0); apply krange_intro; cbn [edenot]; ev_simpl E; [lia|];
                    destruct (Hin8 ltac:(assumption)) as (A1 & A2 & A3); lia |];
      constructor; [pose proof (u64_range g16); destruct (Z.eq_dec _ 0); apply krange_intro; cbn [edenot]; ev_simpl E; [lia|];
                    destruct (Hin16 ltac:(assumption)) as (A1 & A2 & A3); lia |];
      constructor; [eapply (kword_intro SEGS E M (EVar 66) sp (-728) 8 (EVar 98) g8);
        [cbn [edenot]; ev_simpl E; exact Hsp | cbn [edenot]; ev_simpl E; reflexivity | lia | lia | lia | lia |
         replace (bv_unsigned sp + -728)%Z with (s - 1016 + 160 + 128)%Z by lia; exact Hg8] |];
      constructor; [eapply (kword_intro SEGS E M (EVar 66) sp (-720) 8 (EVar 99) g16);
        [cbn [edenot]; ev_simpl E; exact Hsp | cbn [edenot]; ev_simpl E; reflexivity | lia | lia | lia | lia |
         replace (bv_unsigned sp + -720)%Z with (s - 1016 + 160 + 136)%Z by lia; exact Hg16] |];
      constructor; [apply krange_intro; cbn [edenot]; ev_simpl E; rewrite u_small by lia; lia |];
      exact (know_ok_app SEGS E M KNB KND HKB HKD)
    | clear HKB HKD ]
    end.
    destruct (Z.eq_dec (bv_unsigned g8) 0) as [Z8|NZ8]; [|specialize (Hin8 NZ8); unfold inDATA in Hin8];
    destruct (Z.eq_dec (bv_unsigned g16) 0) as [Z16|NZ16]; try (specialize (Hin16 NZ16); unfold inDATA in Hin16).
    all: run_fp 100%nat [0x1311c%Z] (dirs [false; false]) false by mlia.
    all: apply phaseC; [base_same H64i | creg (10%bv:reg) | exact HP | exact Hoc].
  Qed.
End Proof.
End LibFuzzUbA.

Module LibFuzzUbB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.skcms.iccprofile_info.images.Ubsan.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PropExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SeqExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.StoreOk OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Hoare OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Frame OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PropExecFP.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExecFP OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExecFPSound OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymRunFP OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDriveFP OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymCallFP OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibDefs OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibFrame OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibFPLib OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibRodata.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PerfKc.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibTagsSpec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibWP1Spec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.FuzzContract LibFuzzUbA.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDriveLZ.
(* [comment removed for export] *)
#[local] Ltac SymDriveFP.ev_simpl E ::= ev_simpl_lz E.
#[local] Ltac SymDriveFP.ev_simpl_in E H ::= ev_simpl_in_lz E H.
(* [comment removed for export] *)
#[local] Ltac SymDriveFP.run_fp_with_h HR HF HK fuel stops scr chints keep extra ::= run_fp_with_h_lz HR HF HK fuel stops scr chints keep extra.
#[local] Ltac SymDriveFP.branch_case_with HR HF HK Hc ::= branch_case_with_lz HR HF HK Hc.
Unset Lia Cache.
Import ListNotations.
Open Scope bv_scope.
Import SXF. Import SXFS.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

#[local] Abbreviation SEGS := Ubsan.M.loaded_segments.

(* [comment removed for export] *)
Ltac in_lit := cbn; repeat (first [left; reflexivity | right]).

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* [comment removed for export] *)
Ltac mlia := intros;
  lazymatch goal with
  | |- context [Z.modulo _ _] => Z.to_euclidean_division_equations; lia
  | |- _ => lia
  end.

Section Proof.
  Hypothesis Hparse : parse_contract SEGS tags_infoub.
  Hypothesis Hgetidx : getidx_contract SEGS tags_infoub.
  Hypothesis Hrte : rte_contract SEGS 0x131b8.

  Variables (FPI : FPState) (regs : bvmap 5 word) (mem rom : word -> option byte).
  Variables (ret sp data : word) (n : Z) (bs : list byte).

  Hypothesis Hra : getr regs 1 = ret.
  Hypothesis Hret : ret_ok ret.
  Hypothesis Hsp : getr regs 2 = sp.
  Hypothesis Ha0 : getr regs 10 = data.
  Hypothesis Ha1 : getr regs 11 = Z_to_bv 64 n.
  Hypothesis Hn : (0 <= n < 2 ^ 26)%Z.
  Hypothesis Hbs : Z.of_nat (length bs) = n.
  Hypothesis Hal : (bv_unsigned sp mod 16 = 0)%Z.
  Hypothesis Hsplo : (1824 <= bv_unsigned sp)%Z.
  Hypothesis Hsphi : (bv_unsigned sp < 2 ^ 47)%Z.
  Hypothesis Hd0 : (0 < bv_unsigned data)%Z.
  Hypothesis Hdhi : (bv_unsigned data + n < 2 ^ 47)%Z.
  Hypothesis Hblob : forall i, (0 <= i < n)%Z ->
      mem (Z_to_bv 64 (bv_unsigned data + i)) = Some (nth (Z.to_nat i) bs (Z_to_bv 8 0)).
  Hypothesis Hstk : store_ok SEGS mem (Z_to_bv 64 (bv_unsigned sp - 1824)) (Z.to_nat 1824) = true.
  Hypothesis Hgfw : store_ok SEGS mem (Z_to_bv 64 0x31400) 4 = true.
  Hypothesis Hgfr : exists gb, rdn SEGS mem (Z_to_bv 64 0x31400) 4 = Some gb.
  Hypothesis Hro : forall i, (0x103ec <= i < 0x10490)%Z -> mem (Z_to_bv 64 i) = None.
  Hypothesis Hdj1 : (bv_unsigned data + n <= bv_unsigned sp - 1824 \/ bv_unsigned sp <= bv_unsigned data)%Z.
  Hypothesis Hdj2 : (bv_unsigned data + n <= 0x31400 \/ 0x31400 + 4 <= bv_unsigned data)%Z.
  Hypothesis Hdj3 : (0x31400 + 4 <= bv_unsigned sp - 1824 \/ bv_unsigned sp <= 0x31400)%Z.

  (* [comment removed for export] *)
  Ltac touch := pose proof (Hparse, Hgetidx, Hrte, @fp_regs FPI, regs, mem, rom, ret, sp, data, n, bs, Hra, Hret, Hsp, Ha0, Ha1,
                            Hn, Hbs, Hal, Hsplo, Hsphi, Hd0, Hdhi, Hblob, Hstk, Hgfw, Hgfr, Hro, Hdj1, Hdj2, Hdj3) as HALL;
                clear HALL.

  #[local] Abbreviation s := (bv_unsigned sp).
  #[local] Abbreviation BIG := [(Z_to_bv 64 (s - 1824), 1824%Z); (Z_to_bv 64 0x31400, 4%Z)].

  #[local] Abbreviation VALS R FR extra := (junk_vals R ++ fjunk_vals FR ++ junk_vals regs ++ Z_to_bv 64 n :: extra).

  (* [comment removed for export] *)
  #[local] Abbreviation Q := (LibFuzzUbA.Q regs mem rom ret sp).
  #[local] Abbreviation MEMB := (LibFuzzUbA.MEMB regs mem ret sp data n bs).
  #[local] Abbreviation BASE := (LibFuzzUbA.BASE regs mem ret sp data n bs).
  #[local] Abbreviation packB := (LibFuzzUbA.packB Hparse Hgetidx Hrte FPI regs mem rom ret sp data n bs Hra Hret Hsp Ha0 Ha1 Hn Hbs Hal Hsplo Hsphi Hd0 Hdhi Hblob Hstk Hgfw Hgfr Hro Hdj1 Hdj2 Hdj3).
  #[local] Abbreviation phaseE := (LibFuzzUbA.phaseE Hparse Hgetidx Hrte FPI regs mem rom ret sp data n bs Hra Hret Hsp Ha0 Ha1 Hn Hbs Hal Hsplo Hsphi Hd0 Hdhi Hblob Hstk Hgfw Hgfr Hro Hdj1 Hdj2 Hdj3).
  #[local] Abbreviation phaseC := (LibFuzzUbA.phaseC Hparse Hgetidx Hrte FPI regs mem rom ret sp data n bs Hra Hret Hsp Ha0 Ha1 Hn Hbs Hal Hsplo Hsphi Hd0 Hdhi Hblob Hstk Hgfw Hgfr Hro Hdj1 Hdj2 Hdj3).
  #[local] Abbreviation phaseB2 := (LibFuzzUbA.phaseB2 Hparse Hgetidx Hrte FPI regs mem rom ret sp data n bs Hra Hret Hsp Ha0 Ha1 Hn Hbs Hal Hsplo Hsphi Hd0 Hdhi Hblob Hstk Hgfw Hgfr Hro Hdj1 Hdj2 Hdj3).

  Ltac rewrite_getr_in H :=
    repeat match goal with G : getr ?R ?r = _ |- _ => rewrite G in H end.

  (* [comment removed for export] *)
  Ltac kcell HK b k n v H :=
    lazymatch type of HK with know_ok _ ?E0 ?M0 ?kn =>
      let KR := fresh "KR" in let Hfl := fresh "Hfl" in
      kread_rdn_fast SEGS E0 M0 kn b k n v HK H;
      lazymatch type of H with ?FL -> _ =>
        assert (Hfl : FL) by (unfold flat, estart; cbn [a_base a_off edenot]; ev_simpl E0; rewrite_getr; rewrite ?u_small by lia; lia);
        specialize (H Hfl); clear Hfl end;
      unfold adenot, v_addi in H; cbn [a_base a_off edenot] in H; ev_simpl_in E0 H; rewrite_getr_in H
    end.
  Ltac kcell_auto HK b k n H :=
    lazymatch type of HK with know_ok _ _ _ ?kn =>
      let r := eval vm_compute in (kread SEGS kn b k n) in
      lazymatch r with Some ?v => kcell HK b k n v H end end.

  Ltac frame_of_log RS fixup :=
    lazymatch goal with
    | |- frame_mod ?M0 (mem_denot ?E0 ?M0 ?log) ?regions =>
        replace regions with (regions_denot E0 RS)
          by (cbn [regions_denot map fst snd]; unfold adenot; cbn [a_base a_off edenot]; ev_simpl E0; fixup; reflexivity);
        apply (frame_mod_mem_denot E0 M0 log RS);
          [ lazymatch goal with H : log_flat _ log |- _ => exact H end
          | repeat (apply Forall_cons); [..|apply Forall_nil]; cbn [fst snd]; unfold flat, estart; cbn [a_base a_off edenot]; ev_simpl E0; fixup; lia
          | vm_compute; reflexivity ]
    end.

  Ltac subst_triv := repeat match goal with H : ?a = ?b |- _ => is_var a; is_var b; subst a end.

  Ltac solve_reg := rewrite_getr; rewrite ?alu_add_lit; rewrite ?u_small by lia;
                    rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; first [reflexivity | f_equal; lia | idtac].
  Ltac creg r := lazymatch goal with HR : regs_ok _ _ ?R' |- getr ?R' _ = _ => regv HR r; solve_reg end.

  (* [comment removed for export] *)
  Ltac base_same H64i :=
    lazymatch goal with |- BASE ?R' ?M' =>
    lazymatch goal with HR : regs_ok ?E ?sr R', HMB : MEMB M' |- _ =>
      split; [creg (2%bv:reg)|];
      split; [lift_id H64i HR;
              lazymatch type of H64i with id (regs_ok _ ?sr0 _) =>
                exact (regs_same_on E sr0 sr regs R' [3; 4; 20; 21; 22; 23; 24; 25; 26; 27]%bv H64i HR ltac:(vm_compute; reflexivity)) end
             | exact HMB ]
    end end.

  (* [comment removed for export] *)
  Ltac call_rte_auto HC :=
    lazymatch goal with |- runs_to _ (@mkst ?I ?R' _ ?M' _) _ =>
    lazymatch goal with HR : regs_ok _ ?sr R' |- _ =>
      lazymatch eval vm_compute in (sr_get sr 10%bv) with
      | EAlu ALU_ADD (EVar 66) (ELit ?k) =>
        let OFF := eval vm_compute in (k + 1016)%Z in
        eapply rt_call;
        [ eapply (Hrte data n bs (Z_to_bv 64 (s - 1016 + OFF)) I R' M' rom _);
          [ regv HR (1%bv:reg); reflexivity
          | apply ret_ok_even; rewrite u_small by lia; reflexivity
          | unfold rte_pre;
            split; [regv HR (10%bv:reg); rewrite_getr; rewrite ?alu_add_lit; f_equal; lia|];
            split; [assumption|];
            split; [rewrite u_small by lia; apply (curves_pick _ _ _ _ _ _ HC); in_lit|];
            split; rewrite u_small by lia; mlia ]
        | cbv beta;
          let FPI' := fresh "FPI" in let regs' := fresh "R" in let mem' := fresh "MC" in
          let Hkeep := fresh "Hkeep" in let Hfkeep := fresh "Hfkeep" in let Hmem := fresh "Hmem" in
          intros FPI' regs' mem' (Hkeep & Hfkeep & Hmem); unfold rte_post in Hmem; subst mem';
          unfold regs_kept in Hkeep; clear Hfkeep;
          after_call Hkeep FPI'; clear Hkeep ]
      end end end.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma zprod_bounds : forall gps, Forall (fun g => 2 <= g <= 255)%Z gps ->
    (1 <= zprod gps <= 255 ^ Z.of_nat (length gps))%Z.
  Proof.
    intros gps H. induction H as [|g gps Hg H IH]; [cbn; lia|].
    cbn [zprod length]. rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. nia.
  Qed.

  (* [comment removed for export] *)
  Definition KGP (o : Z) (i : nat) : list kentry := [KWord (SA (EVar 66) o) 1 (EVar i); KRange (EVar i) 2 255].
  Definition KGPS (k : nat) : list kentry :=
    match k with
    | 0 => []
    | 1 => KGP (-708) 100
    | 2 => KGP (-708) 100 ++ KGP (-707) 101
    | 3 => KGP (-708) 100 ++ KGP (-707) 101 ++ KGP (-706) 102
    | _ => KGP (-708) 100 ++ KGP (-707) 101 ++ KGP (-706) 102 ++ KGP (-705) 103
    end%nat.
  Definition KNA2B (k : nat) : list kentry :=
    KWord (SA (EVar 66) (-50)) 1 (ELit 1) :: KWord (SA (EVar 66) (-712)) 4 (ELit (Z.of_nat k)) ::
    KWord (SA (EVar 66) (-556)) 4 (ELit 3) :: KWord (SA (EVar 66) (-728)) 8 (EVar 98) :: KWord (SA (EVar 66) (-720)) 8 (EVar 99) ::
    KGPS k ++ KNB ++ KND.

  (* [comment removed for export] *)
  Lemma mul3_word : forall a b : Z, (0 <= a < 2 ^ 64)%Z -> (0 <= b < 2 ^ 64)%Z ->
    mul_div M_MUL (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a * b).
  Proof.
    intros a b Ha Hb. rewrite m_mul. unfold v_mul. rewrite !u_small by lia. reflexivity.
  Qed.

  Lemma phaseB : forall (FPX : FPState) R M, BASE R M ->
    parsed_ok SEGS M data n bs (s - 1016) ->
    runs_to SEGS (mkst (FP:=FPX) R (Z_to_bv 64 0x13028) M rom) Q.
  Proof.
    touch.
    intros FPX R M HB HP. pose proof HB as (R2 & RK & HMB).
    pose proof HMB as (_ & _ & _ & _ & _ & Mfr & Mw & Mg & Mc & Mro & Md).
    destruct Mc as [gw Hgw].
    pose proof HP as (psz & tc & htrc & hasA2B & _ & _ & _ & _ & HC & _ & _ & [Hh1 H966] & Hha & Hgrid).
    pose proof (u64_range sp) as Hspr. pose proof (u64_range data) as Hdr.
    unfold cell in H966.
    destruct Hha as [Hha | Hha]; rewrite Hha in H966.
    { (* [comment removed for export] *)
      destruct (packB R (fp_regs (FPState:=FPX)) M gw [] HB Hgw) as (HR & HF & HKB & _ & H64).
      pose proof (H64 : id _) as H64i. clear H64.
      lazymatch type of HR with regs_ok ?E _ _ =>
        assert (HK : know_ok SEGS E M (KWord (SA (EVar 66) (-50)) 1 (ELit 0) :: KNB));
        [ constructor; [| exact HKB];
          eapply (kword_intro SEGS E M (EVar 66) sp (-50) 1 (ELit 0) (Z_to_bv 64 0));
            [cbn [edenot]; ev_simpl E; exact Hsp | reflexivity | lia | lia | lia | lia |
             replace (bv_unsigned sp + -50)%Z with (s - 1016 + 966)%Z by lia; exact H966]
        | clear HKB ] end.
      run_fp 100%nat [0x13194%Z] noscr false. apply phaseE. base_same H64i. }
    (* [comment removed for export] *)
    destruct (Hgrid ltac:(rewrite Hha; lia)) as (ic & oc & gps & g8 & g16 & [_ Hic] & [_ Hoc] & Hicr & Hlen & Hgps & Hgp & Hg8 & Hg16 & Hoc3 & Hin).
    subst oc. unfold cell in Hic, Hoc. unfold cell64, cell in Hg8, Hg16.
    pose proof (zprod_bounds gps Hgps) as HZP.
    pose proof (u64_range g8) as Hg8r. pose proof (u64_range g16) as Hg16r.
    rewrite Forall_forall in Hgps.
    (* [comment removed for export] *)
    Ltac caseB EXTRA H966 Hic Hoc Hg8 Hg16 Hgp Hlen HB Hgw :=
      lazymatch goal with |- runs_to _ (@mkst ?FPX ?R _ ?M _) _ =>
      let T := fresh "T" in
      destruct (packB R (fp_regs (FPState:=FPX)) M _ EXTRA HB Hgw) as (HR & HF & HKB & HKD & H64);
      pose proof (H64 : id _) as H64i; clear H64;
      lazymatch type of HR with regs_ok ?E _ _ =>
      lazymatch type of Hlen with Z.of_nat ?k = _ =>
        assert (HK : know_ok SEGS E M (KNA2B k));
        [ unfold KNA2B;
          constructor; [eapply (kword_intro SEGS E M (EVar 66) sp (-50) 1 (ELit 1) (Z_to_bv 64 1));
              [cbn [edenot]; ev_simpl E; exact Hsp | reflexivity | lia | lia | lia | lia |
               replace (bv_unsigned sp + -50)%Z with (s - 1016 + 966)%Z by lia; exact H966] |];
          constructor; [eapply (kword_intro SEGS E M (EVar 66) sp (-712) 4 (ELit (Z.of_nat k)) (Z_to_bv 64 (Z.of_nat k)));
              [cbn [edenot]; ev_simpl E; exact Hsp | reflexivity | lia | lia | lia | lia |
               replace (bv_unsigned sp + -712)%Z with (s - 1016 + 160 + 144)%Z by lia; exact Hic] |];
          constructor; [eapply (kword_intro SEGS E M (EVar 66) sp (-556) 4 (ELit 3) (Z_to_bv 64 3));
              [cbn [edenot]; ev_simpl E; exact Hsp | reflexivity | lia | lia | lia | lia |
               replace (bv_unsigned sp + -556)%Z with (s - 1016 + 160 + 300)%Z by lia; exact Hoc] |];
          constructor; [eapply (kword_intro SEGS E M (EVar 66) sp (-728) 8 (EVar 98) _);
              [cbn [edenot]; ev_simpl E; exact Hsp | cbn [edenot]; ev_simpl E; reflexivity | lia | lia | lia | lia |
               replace (bv_unsigned sp + -728)%Z with (s - 1016 + 160 + 128)%Z by lia; exact Hg8] |];
          constructor; [eapply (kword_intro SEGS E M (EVar 66) sp (-720) 8 (EVar 99) _);
              [cbn [edenot]; ev_simpl E; exact Hsp | cbn [edenot]; ev_simpl E; reflexivity | lia | lia | lia | lia |
               replace (bv_unsigned sp + -720)%Z with (s - 1016 + 160 + 136)%Z by lia; exact Hg16] |];
          apply know_ok_app; [| exact (know_ok_app SEGS E M KNB KND HKB HKD)];
          unfold KGPS, KGP; cbn [app];
          repeat lazymatch goal with
          | |- ?hd (KWord (SA _ ?o) 1 (EVar ?i) :: KRange _ 2 255 :: _) =>
              let j := eval cbv in (Z.of_nat (i - 100)%nat) in
              let Hb := fresh "Hb" in let Hb1 := fresh "Hb1" in let Hb2 := fresh "Hb2" in
              pose proof (Hgp j ltac:(lia)) as Hb; destruct Hb as [Hb1 Hb2]; unfold cell in Hb2;
              cbn [Z.to_nat Pos.to_nat nth Pos.iter_op Nat.add] in Hb1, Hb2;
              constructor; [eapply (kword_intro SEGS E M (EVar 66) sp o 1 (EVar i));
                [cbn [edenot]; ev_simpl E; exact Hsp | cbn [edenot]; ev_simpl E; reflexivity | lia | lia | lia | lia |
                 lazymatch type of Hb2 with rdn _ _ (Z_to_bv 64 ?b) _ = _ => replace (bv_unsigned sp + o)%Z with b by lia; exact Hb2 end] |];
              constructor; [apply krange_intro; cbn [edenot]; ev_simpl E; rewrite u_small by lia; lia |];
              clear Hb1 Hb2
          | |- ?hd [] => constructor
          end
        | clear HKB HKD ]
      end end end.
    (* [comment removed for export] *)
    Ltac callsB HC :=
      run_fp 100%nat [0x131b8%Z; 0x130bc%Z] noscr false;
      lazymatch goal with
      | |- runs_to _ (mkst _ (Z_to_bv 64 0x131b8) _ _) _ => call_rte_auto HC; callsB HC
      | |- _ => idtac
      end.
    Ltac finishB GPS H64i HP Hoc Hg8 Hg16 Hin :=
      eapply (phaseB2 _ _ _ _ _ (3 * zprod GPS)%Z);
        [ base_same H64i | creg (10%bv:reg)
        | lazymatch goal with HR : regs_ok _ _ ?R' |- getr ?R' _ = _ => regv HR (11%bv:reg) end;
          repeat (rewrite mul3_word by (cbn [zprod] in *; nia)); f_equal; cbn [zprod]; nia
        | exact HP
        | exact Hoc
        | exact Hg8
        | exact Hg16
        | exact (proj1 (Hin ltac:(lia)))
        | exact (proj2 (Hin ltac:(lia)))
        | cbn [zprod length Z.of_nat Pos.of_succ_nat Pos.succ Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul] in *; nia ].
    destruct gps as [|g0 [|g1 [|g2 [|g3 [|g4 gps']]]]]; cbn [length] in Hlen, HZP; subst ic;
      [ | | | | | exfalso; lia ].
    - caseB [g8; g16] H966 Hic Hoc Hg8 Hg16 Hgp (eq_refl (Z.of_nat 0)) HB Hgw.
      run_fp 100%nat [0x1311c%Z] noscr false. apply phaseC; [base_same H64i | creg (10%bv:reg) | exact HP | exact Hoc].
    - pose proof (Hgps g0 ltac:(in_lit)) as G0.
      caseB [g8; g16; Z_to_bv 64 g0] H966 Hic Hoc Hg8 Hg16 Hgp (eq_refl (Z.of_nat 1)) HB Hgw.
      callsB HC. finishB [g0] H64i HP Hoc Hg8 Hg16 Hin.
    - pose proof (Hgps g0 ltac:(in_lit)) as G0. pose proof (Hgps g1 ltac:(in_lit)) as G1.
      caseB [g8; g16; Z_to_bv 64 g0; Z_to_bv 64 g1] H966 Hic Hoc Hg8 Hg16 Hgp (eq_refl (Z.of_nat 2)) HB Hgw.
      callsB HC. finishB [g0; g1] H64i HP Hoc Hg8 Hg16 Hin.
    - pose proof (Hgps g0 ltac:(in_lit)) as G0. pose proof (Hgps g1 ltac:(in_lit)) as G1. pose proof (Hgps g2 ltac:(in_lit)) as G2.
      caseB [g8; g16; Z_to_bv 64 g0; Z_to_bv 64 g1; Z_to_bv 64 g2] H966 Hic Hoc Hg8 Hg16 Hgp (eq_refl (Z.of_nat 3)) HB Hgw.
      callsB HC. finishB [g0; g1; g2] H64i HP Hoc Hg8 Hg16 Hin.
    - pose proof (Hgps g0 ltac:(in_lit)) as G0. pose proof (Hgps g1 ltac:(in_lit)) as G1. pose proof (Hgps g2 ltac:(in_lit)) as G2.
      pose proof (Hgps g3 ltac:(in_lit)) as G3.
      caseB [g8; g16; Z_to_bv 64 g0; Z_to_bv 64 g1; Z_to_bv 64 g2; Z_to_bv 64 g3] H966 Hic Hoc Hg8 Hg16 Hgp (eq_refl (Z.of_nat 4)) HB Hgw.
      callsB HC. finishB [g0; g1; g2; g3] H64i HP Hoc Hg8 Hg16 Hin.
  Qed.


End Proof.
End LibFuzzUbB.

(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.skcms.iccprofile_info.images Require Import Ubsan.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import PropExec CatExec CatSim SeqExec StoreOk SymExec Hoare Frame PropExecFP.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import SymExecFP SymExecFPSound SymRunFP SymDriveFP SymCallFP LibDefs LibFrame LibFPLib LibRodata.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import PerfKc.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import LibTagsSpec LibWP1Spec FuzzContract. Import LibFuzzUbA. Import LibFuzzUbB.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import SymDriveLZ.
(* [comment removed for export] *)
#[local] Ltac SymDriveFP.ev_simpl E ::= ev_simpl_lz E.
#[local] Ltac SymDriveFP.ev_simpl_in E H ::= ev_simpl_in_lz E H.
(* [comment removed for export] *)
#[local] Ltac SymDriveFP.run_fp_with_h HR HF HK fuel stops scr chints keep extra ::= run_fp_with_h_lz HR HF HK fuel stops scr chints keep extra.
#[local] Ltac SymDriveFP.branch_case_with HR HF HK Hc ::= branch_case_with_lz HR HF HK Hc.
Unset Lia Cache.
Import ListNotations.
Open Scope bv_scope.
Import SXF. Import SXFS.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

#[local] Abbreviation SEGS := Ubsan.M.loaded_segments.

(* [comment removed for export] *)
Ltac in_lit := cbn; repeat (first [left; reflexivity | right]).

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* [comment removed for export] *)
Ltac mlia := intros;
  lazymatch goal with
  | |- context [Z.modulo _ _] => Z.to_euclidean_division_equations; lia
  | |- _ => lia
  end.

Section Proof.
  Hypothesis Hparse : parse_contract SEGS tags_infoub.
  Hypothesis Hgetidx : getidx_contract SEGS tags_infoub.
  Hypothesis Hrte : rte_contract SEGS 0x131b8.

  Variables (FPI : FPState) (regs : bvmap 5 word) (mem rom : word -> option byte).
  Variables (ret sp data : word) (n : Z) (bs : list byte).

  Hypothesis Hra : getr regs 1 = ret.
  Hypothesis Hret : ret_ok ret.
  Hypothesis Hsp : getr regs 2 = sp.
  Hypothesis Ha0 : getr regs 10 = data.
  Hypothesis Ha1 : getr regs 11 = Z_to_bv 64 n.
  Hypothesis Hn : (0 <= n < 2 ^ 26)%Z.
  Hypothesis Hbs : Z.of_nat (length bs) = n.
  Hypothesis Hal : (bv_unsigned sp mod 16 = 0)%Z.
  Hypothesis Hsplo : (1824 <= bv_unsigned sp)%Z.
  Hypothesis Hsphi : (bv_unsigned sp < 2 ^ 47)%Z.
  Hypothesis Hd0 : (0 < bv_unsigned data)%Z.
  Hypothesis Hdhi : (bv_unsigned data + n < 2 ^ 47)%Z.
  Hypothesis Hblob : forall i, (0 <= i < n)%Z ->
      mem (Z_to_bv 64 (bv_unsigned data + i)) = Some (nth (Z.to_nat i) bs (Z_to_bv 8 0)).
  Hypothesis Hstk : store_ok SEGS mem (Z_to_bv 64 (bv_unsigned sp - 1824)) (Z.to_nat 1824) = true.
  Hypothesis Hgfw : store_ok SEGS mem (Z_to_bv 64 0x31400) 4 = true.
  Hypothesis Hgfr : exists gb, rdn SEGS mem (Z_to_bv 64 0x31400) 4 = Some gb.
  Hypothesis Hro : forall i, (0x103ec <= i < 0x10490)%Z -> mem (Z_to_bv 64 i) = None.
  Hypothesis Hdj1 : (bv_unsigned data + n <= bv_unsigned sp - 1824 \/ bv_unsigned sp <= bv_unsigned data)%Z.
  Hypothesis Hdj2 : (bv_unsigned data + n <= 0x31400 \/ 0x31400 + 4 <= bv_unsigned data)%Z.
  Hypothesis Hdj3 : (0x31400 + 4 <= bv_unsigned sp - 1824 \/ bv_unsigned sp <= 0x31400)%Z.

  (* [comment removed for export] *)
  Ltac touch := pose proof (Hparse, Hgetidx, Hrte, @fp_regs FPI, regs, mem, rom, ret, sp, data, n, bs, Hra, Hret, Hsp, Ha0, Ha1,
                            Hn, Hbs, Hal, Hsplo, Hsphi, Hd0, Hdhi, Hblob, Hstk, Hgfw, Hgfr, Hro, Hdj1, Hdj2, Hdj3) as HALL;
                clear HALL.

  #[local] Abbreviation s := (bv_unsigned sp).
  #[local] Abbreviation BIG := [(Z_to_bv 64 (s - 1824), 1824%Z); (Z_to_bv 64 0x31400, 4%Z)].

  #[local] Abbreviation VALS R FR extra := (junk_vals R ++ fjunk_vals FR ++ junk_vals regs ++ Z_to_bv 64 n :: extra).

  (* [comment removed for export] *)
  #[local] Abbreviation Q := (LibFuzzUbA.Q regs mem rom ret sp).
  #[local] Abbreviation MEMB := (LibFuzzUbA.MEMB regs mem ret sp data n bs).
  #[local] Abbreviation BASE := (LibFuzzUbA.BASE regs mem ret sp data n bs).
  #[local] Abbreviation packB := (LibFuzzUbA.packB Hparse Hgetidx Hrte FPI regs mem rom ret sp data n bs Hra Hret Hsp Ha0 Ha1 Hn Hbs Hal Hsplo Hsphi Hd0 Hdhi Hblob Hstk Hgfw Hgfr Hro Hdj1 Hdj2 Hdj3).
  #[local] Abbreviation memb_frame_gf := (LibFuzzUbA.memb_frame_gf Hparse Hgetidx Hrte FPI regs mem rom ret sp data n bs Hra Hret Hsp Ha0 Ha1 Hn Hbs Hal Hsplo Hsphi Hd0 Hdhi Hblob Hstk Hgfw Hgfr Hro Hdj1 Hdj2 Hdj3).
  #[local] Abbreviation memb_frame_in := (LibFuzzUbA.memb_frame_in Hparse Hgetidx Hrte FPI regs mem rom ret sp data n bs Hra Hret Hsp Ha0 Ha1 Hn Hbs Hal Hsplo Hsphi Hd0 Hdhi Hblob Hstk Hgfw Hgfr Hro Hdj1 Hdj2 Hdj3).
  #[local] Abbreviation phaseE := (LibFuzzUbA.phaseE Hparse Hgetidx Hrte FPI regs mem rom ret sp data n bs Hra Hret Hsp Ha0 Ha1 Hn Hbs Hal Hsplo Hsphi Hd0 Hdhi Hblob Hstk Hgfw Hgfr Hro Hdj1 Hdj2 Hdj3).
  #[local] Abbreviation phaseB := (LibFuzzUbB.phaseB Hparse Hgetidx Hrte FPI regs mem rom ret sp data n bs Hra Hret Hsp Ha0 Ha1 Hn Hbs Hal Hsplo Hsphi Hd0 Hdhi Hblob Hstk Hgfw Hgfr Hro Hdj1 Hdj2 Hdj3).

  (* [comment removed for export] *)
  Lemma data_ok0 : data_ok mem data n bs.
  Proof. split; [exact Hn|]. split; [exact Hbs|]. split; [exact Hd0|]. split; [exact Hdhi|]. exact Hblob. Qed.

  Lemma writable0 : writable SEGS mem (s - 1824) 1824.
  Proof. pose proof (u64_range sp). split; [mlia|]. split; [mlia|]. split; [mlia|]. exact Hstk. Qed.

  Lemma gfool0 : writable SEGS mem 0x31400 4 /\ exists gw, cell SEGS mem 0x31400 4 gw.
  Proof.
    split; [split; [mlia|]; split; [mlia|]; split; [mlia|]; exact Hgfw|].
    destruct Hgfr as [gb Hgb]. exact (cell_of_rdn SEGS mem 0x31400 4 gb Hgb ltac:(lia)).
  Qed.

  Ltac rewrite_getr_in H :=
    repeat match goal with G : getr ?R ?r = _ |- _ => rewrite G in H end.

  (* [comment removed for export] *)
  Ltac kcell HK b k n v H :=
    lazymatch type of HK with know_ok _ ?E0 ?M0 ?kn =>
      let KR := fresh "KR" in let Hfl := fresh "Hfl" in
      kread_rdn_fast SEGS E0 M0 kn b k n v HK H;
      lazymatch type of H with ?FL -> _ =>
        assert (Hfl : FL) by (unfold flat, estart; cbn [a_base a_off edenot]; ev_simpl E0; rewrite_getr; rewrite ?u_small by lia; lia);
        specialize (H Hfl); clear Hfl end;
      unfold adenot, v_addi in H; cbn [a_base a_off edenot] in H; ev_simpl_in E0 H; rewrite_getr_in H
    end.
  Ltac kcell_auto HK b k n H :=
    lazymatch type of HK with know_ok _ _ _ ?kn =>
      let r := eval vm_compute in (kread SEGS kn b k n) in
      lazymatch r with Some ?v => kcell HK b k n v H end end.

  Ltac frame_of_log RS fixup :=
    lazymatch goal with
    | |- frame_mod ?M0 (mem_denot ?E0 ?M0 ?log) ?regions =>
        replace regions with (regions_denot E0 RS)
          by (cbn [regions_denot map fst snd]; unfold adenot; cbn [a_base a_off edenot]; ev_simpl E0; fixup; reflexivity);
        apply (frame_mod_mem_denot E0 M0 log RS);
          [ lazymatch goal with H : log_flat _ log |- _ => exact H end
          | repeat (apply Forall_cons); [..|apply Forall_nil]; cbn [fst snd]; unfold flat, estart; cbn [a_base a_off edenot]; ev_simpl E0; fixup; lia
          | vm_compute; reflexivity ]
    end.

  Ltac subst_triv := repeat match goal with H : ?a = ?b |- _ => is_var a; is_var b; subst a end.

  Ltac solve_reg := rewrite_getr; rewrite ?alu_add_lit; rewrite ?u_small by lia;
                    rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; first [reflexivity | f_equal; lia | idtac].
  Ltac creg r := lazymatch goal with HR : regs_ok _ _ ?R' |- getr ?R' _ = _ => regv HR r; solve_reg end.

  (* [comment removed for export] *)
  Ltac base_same H64i :=
    lazymatch goal with |- BASE ?R' ?M' =>
    lazymatch goal with HR : regs_ok ?E ?sr R', HMB : MEMB M' |- _ =>
      split; [creg (2%bv:reg)|];
      split; [lift_id H64i HR;
              lazymatch type of H64i with id (regs_ok _ ?sr0 _) =>
                exact (regs_same_on E sr0 sr regs R' [3; 4; 20; 21; 22; 23; 24; 25; 26; 27]%bv H64i HR ltac:(vm_compute; reflexivity)) end
             | exact HMB ]
    end end.

  (* [comment removed for export] *)
  Ltac call_rte_auto HC :=
    lazymatch goal with |- runs_to _ (@mkst ?I ?R' _ ?M' _) _ =>
    lazymatch goal with HR : regs_ok _ ?sr R' |- _ =>
      lazymatch eval vm_compute in (sr_get sr 10%bv) with
      | EAlu ALU_ADD (EVar 66) (ELit ?k) =>
        let OFF := eval vm_compute in (k + 1016)%Z in
        eapply rt_call;
        [ eapply (Hrte data n bs (Z_to_bv 64 (s - 1016 + OFF)) I R' M' rom _);
          [ regv HR (1%bv:reg); reflexivity
          | apply ret_ok_even; rewrite u_small by lia; reflexivity
          | unfold rte_pre;
            split; [regv HR (10%bv:reg); rewrite_getr; rewrite ?alu_add_lit; f_equal; lia|];
            split; [assumption|];
            split; [rewrite u_small by lia; apply (curves_pick _ _ _ _ _ _ HC); in_lit|];
            split; rewrite u_small by lia; mlia ]
        | cbv beta;
          let FPI' := fresh "FPI" in let regs' := fresh "R" in let mem' := fresh "MC" in
          let Hkeep := fresh "Hkeep" in let Hfkeep := fresh "Hfkeep" in let Hmem := fresh "Hmem" in
          intros FPI' regs' mem' (Hkeep & Hfkeep & Hmem); unfold rte_post in Hmem; subst mem';
          unfold regs_kept in Hkeep; clear Hfkeep;
          after_call Hkeep FPI'; clear Hkeep ]
      end end end.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac after_gf_store :=
    lazymatch goal with EQM : ?M1 = mem_denot ?E0 ?M0 ?log |- _ =>
    lazymatch goal with HMB0 : MEMB M0, HP0 : parsed_ok _ M0 _ _ _ _, HK : know_ok _ _ M1 _ |- _ =>
      let Hf := fresh "Hgf" in let HG := fresh "HG" in
      assert (Hf : frame_mod M0 M1 [(Z_to_bv 64 0x31400, 4%Z)])
        by (rewrite EQM; frame_of_log [(SA (ELit 0) 0x31400, 4%Z)] ltac:(change (bv_unsigned (Z_to_bv 64 0) + 0x31400)%Z with 0x31400%Z));
      kcell_auto HK (ELit 0) 0x31400%Z 4%nat HG; rewrite u_small in HG by lia;
      let HMB1 := fresh "HMB" in let HP1 := fresh "HP" in
      pose proof (memb_frame_gf M0 M1 HMB0 Hf (ex_intro _ _ HG)) as HMB1;
      pose proof (parsed_ok_frame SEGS M0 M1 _ data n bs (s - 1016) Hf HP0 ltac:(lia) ltac:(lia)
                    ltac:(solve_apart)) as HP1;
      clear HG Hf EQM; try clear HMB0; try clear HP0;
      try (lazymatch goal with HLF : log_flat _ _ |- _ => clear HLF end)
    end end.

  Lemma phaseA2 : forall (FPX : FPState) R M, BASE R M ->
    parsed_ok SEGS M data n bs (s - 1016) ->
    runs_to SEGS (mkst (FP:=FPX) R (Z_to_bv 64 0x12fec) M rom) Q.
  Proof.
    touch.
    intros FPX R M HB HP. pose proof HB as (R2 & RK & HMB).
    pose proof HMB as (_ & _ & _ & _ & _ & Mfr & Mw & Mg & Mc & Mro & Md).
    destruct Mc as [gw Hgw].
    pose proof HP as (psz & tc & htrc & hasA2B & _ & _ & _ & _ & HC & [Hh1 H964] & Hht & _).
    pose proof (u64_range sp) as Hspr. pose proof (u64_range data) as Hdr.
    unfold cell in H964.
    destruct (packB R (fp_regs (FPState:=FPX)) M gw [] HB Hgw) as (HR & HF & HKB & _ & H64).
    pose proof (H64 : id _) as H64i. clear H64.
    lazymatch type of HR with regs_ok ?E _ _ =>
      assert (HK : know_ok SEGS E M (KWord (SA (EVar 66) (-52)) 1 (ELit htrc) :: KNB));
      [ constructor; [| exact HKB];
        eapply (kword_intro SEGS E M (EVar 66) sp (-52) 1 (ELit htrc) (Z_to_bv 64 htrc));
          [cbn [edenot]; ev_simpl E; exact Hsp | reflexivity | lia | lia | lia | lia |
           replace (bv_unsigned sp + -52)%Z with (s - 1016 + 964)%Z by lia; exact H964]
      | clear HKB ] end.
    destruct Hht as [Hht | Hht]; rewrite Hht in HK.
    { (* [comment removed for export] *)
      run_fp 100%nat [0x13028%Z] noscr false. apply phaseB; [base_same H64i | exact HP]. }
    (* [comment removed for export] *)
    clear Mfr Mw Mg Mro.
    run_fp 100%nat [0x131b8%Z] noscr false.
    call_rte_auto HC.
    run_fp 100%nat [0x131b8%Z] noscr true; subst_triv. after_gf_store.
    lazymatch goal with HP1 : parsed_ok _ ?M1 _ _ _ _, HMB1 : MEMB ?M1 |- runs_to _ (@mkst _ _ _ ?M1 _) _ =>
      pose proof HP1 as (? & ? & ? & ? & _ & _ & _ & _ & HC1 & _);
      pose proof HMB1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Md1);
      call_rte_auto HC1; clear HC1 Md1 end.
    run_fp 100%nat [0x131b8%Z] noscr true; subst_triv. after_gf_store.
    lazymatch goal with HP1 : parsed_ok _ ?M1 _ _ _ _, HMB1 : MEMB ?M1 |- runs_to _ (@mkst _ _ _ ?M1 _) _ =>
      pose proof HP1 as (? & ? & ? & ? & _ & _ & _ & _ & HC1 & _);
      pose proof HMB1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Md1);
      call_rte_auto HC1; clear HC1 Md1 end.
    run_fp 100%nat [0x13028%Z] noscr true; subst_triv. after_gf_store.
    lazymatch goal with HP1 : parsed_ok _ ?M1 _ _ _ _, HMB1 : MEMB ?M1 |- runs_to _ (@mkst _ ?R' _ ?M1 _) _ =>
      apply phaseB; [ | exact HP1];
      split; [creg (2%bv:reg)|];
      split; [lift_id H64i HR;
              lazymatch type of HR with regs_ok ?E ?sr _ =>
              lazymatch type of H64i with id (regs_ok _ ?sr0 _) =>
                exact (regs_same_on E sr0 sr regs R' [3; 4; 20; 21; 22; 23; 24; 25; 26; 27]%bv H64i HR ltac:(vm_compute; reflexivity)) end end
             | exact HMB1 ] end.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac call_getidx IDX H0 Htc Htags Md Mw :=
    lazymatch goal with |- runs_to _ (@mkst ?I ?R' _ ?M' _) _ =>
    lazymatch goal with HR : regs_ok _ _ R' |- _ =>
      lazymatch type of Htags with tags_ok _ _ ?tc ?psz =>
      eapply rt_call;
      [ eapply (Hgetidx data n bs (Z_to_bv 64 (s - 1016)) tc psz IDX (Z_to_bv 64 (s - 1040)) I R' M' rom _);
        [ regv HR (1%bv:reg); reflexivity
        | apply ret_ok_even; rewrite u_small by lia; reflexivity
        | unfold getidx_pre; cbv zeta;
          split; [regv HR (10%bv:reg); rewrite_getr; rewrite ?alu_add_lit; f_equal; lia|];
          split; [regv HR (11%bv:reg); first [reflexivity | rewrite (addw_small _ (-1) (IDX + 1)) by (rewrite ?u_small by lia; lia); f_equal; lia]|];
          split; [regv HR (12%bv:reg); rewrite_getr; rewrite ?alu_add_lit; f_equal; lia|];
          split; [mlia|];
          split; [exact Md|];
          rewrite !u_small by lia;
          split; [exact H0|]; split; [split; [lia| exact Htc]|]; split; [exact Htags|];
          split; [mlia|]; split; [mlia|]; split; [mlia|]; split; [mlia|]; split; [mlia|];
          split; [eapply (writable_sub _ _ _ _ _ _ Mw); lia |];
          lia ]
      | cbv beta;
        let FPI' := fresh "FPI" in let regs' := fresh "R" in let mem' := fresh "MG" in
        let Hkeep := fresh "Hkeep" in let Hfkeep := fresh "Hfkeep" in let Hpost := fresh "Hpost" in let Hfr := fresh "Hfr" in
        intros FPI' regs' mem' (Hkeep & Hfkeep & Hpost);
        unfold getidx_post in Hpost; cbv zeta in Hpost; destruct Hpost as (Hfr & _);
        unfold regs_kept in Hkeep; clear Hfkeep; after_call Hkeep FPI'; clear Hkeep;
        lazymatch goal with HK : know_ok _ _ M' _ |- _ => know_frame HK Hfr [(SA (EVar 66) (-1040), 24%Z)] end;
        [ rewrite Hsp; unfold v_addi; repeat f_equal; lia | ] ]
    end end end.

  (* [comment removed for export] *)
  Lemma getidx_frame : forall M M', MEMB M -> parsed_ok SEGS M data n bs (s - 1016) ->
    frame_mod M M' [(Z_to_bv 64 (s - 1040), 24%Z)] ->
    MEMB M' /\ parsed_ok SEGS M' data n bs (s - 1016).
  Proof.
    intros M M' HMB HP Hf. pose proof (u64_range sp). split.
    - eapply memb_frame_in; [exact HMB | exact Hf |]. constructor; [|constructor]. cbn [fst snd]. rewrite u_small by lia. lia.
    - eapply parsed_ok_frame; [exact Hf | exact HP | lia | lia | solve_apart].
  Qed.

  Lemma phaseA1 : forall (FPX : FPState) R M (r : Z), BASE R M ->
    getr R 10 = Z_to_bv 64 r -> (r = 0 \/ r = 1)%Z ->
    (r = 1%Z -> parsed_ok SEGS M data n bs (s - 1016)) ->
    runs_to SEGS (mkst (FP:=FPX) R (Z_to_bv 64 0x12fbc) M rom) Q.
  Proof.
    touch.
    intros FPX R M r HB R10 Hr HPr. pose proof HB as (R2 & RK & HMB).
    pose proof HMB as (_ & _ & _ & _ & _ & Mfr & Mw & Mg & Mc & Mro & Md).
    destruct Mc as [gw Hgw].
    pose proof (u64_range sp) as Hspr. pose proof (u64_range data) as Hdr.
    destruct Hr as [Hr | Hr]; subst r.
    { (* [comment removed for export] *)
      destruct (packB R (fp_regs (FPState:=FPX)) M gw [] HB Hgw) as (HR & HF & HK & _ & H64).
      pose proof (H64 : id _) as H64i. clear H64.
      apply (regs_ok_pin _ _ R 10 (ELit 0)) in HR; [| exact R10].
      run_fp 100%nat [0x13194%Z] noscr false. apply phaseE. base_same H64i. }
    specialize (HPr eq_refl). pose proof HPr as HP.
    destruct HPr as (psz & tc & htrc & hasA2B & H0 & H8 & [Htc32 Htc] & Htags & _).
    unfold cell64, cell in H0. unfold cell in Htc.
    pose proof Htags as (Htc0 & Hpsz & _).
    destruct (Z.eq_dec tc 0) as [Htz | Htnz].
    { (* [comment removed for export] *)
      subst tc.
      destruct (packB R (fp_regs (FPState:=FPX)) M gw [] HB Hgw) as (HR & HF & HKB & _ & H64).
      pose proof (H64 : id _) as H64i. clear H64.
      apply (regs_ok_pin _ _ R 10 (ELit 1)) in HR; [| exact R10].
      lazymatch type of HR with regs_ok ?E _ _ =>
        assert (HK : know_ok SEGS E M (KWord (SA (EVar 66) (-996)) 4 (ELit 0) :: KNB));
        [ constructor; [| exact HKB];
          eapply (kword_intro SEGS E M (EVar 66) sp (-996) 4 (ELit 0) (Z_to_bv 64 0));
            [cbn [edenot]; ev_simpl E; exact Hsp | reflexivity | lia | lia | lia | lia |
             replace (bv_unsigned sp + -996)%Z with (s - 1016 + 20)%Z by lia; exact Htc]
        | clear HKB ] end.
      run_fp 100%nat [0x12fec%Z] noscr false. apply phaseA2; [base_same H64i | exact HP]. }
    (* [comment removed for export] *)
    destruct (packB R (fp_regs (FPState:=FPX)) M gw [Z_to_bv 64 tc] HB Hgw) as (HR & HF & HKB & _ & H64).
    pose proof (H64 : id _) as H64i. clear H64.
    apply (regs_ok_pin _ _ R 10 (ELit 1)) in HR; [| exact R10].
    lazymatch type of HR with regs_ok ?E _ _ =>
      assert (HK : know_ok SEGS E M (KWord (SA (EVar 66) (-996)) 4 (EVar 98) :: KRange (EVar 98) 1 5592405 :: KNB));
      [ constructor; [| constructor; [| exact HKB]];
        [ eapply (kword_intro SEGS E M (EVar 66) sp (-996) 4 (EVar 98) (Z_to_bv 64 tc));
            [cbn [edenot]; ev_simpl E; exact Hsp | cbn [edenot]; ev_simpl E; reflexivity | lia | lia | lia | lia |
             replace (bv_unsigned sp + -996)%Z with (s - 1016 + 20)%Z by lia; exact Htc]
        | apply krange_intro; cbn [edenot]; ev_simpl E; rewrite u_small by lia; lia ]
      | clear HKB ] end.
    clear Mfr Mg Mro.
    run_fp 100%nat [0x13cfc%Z] noscr false.
    call_getidx 0%Z H0 Htc Htags Md Mw.
    destruct (getidx_frame _ _ HMB HP Hfr) as [HMB1 HP1].
    lazymatch type of Hfr with frame_mod _ ?M1 _ =>
      assert (H0' : cell SEGS M1 (s - 1016) 8 data) by (eapply cell_frame; [exact Hfr | exact H0 | lia | cbn; lia | solve_apart]);
      assert (Htc' : cell SEGS M1 (s - 1016 + 20) 4 (Z_to_bv 64 tc)) by (eapply cell_frame; [exact Hfr | exact Htc | lia | cbn; lia | solve_apart])
    end.
    unfold cell in H0', Htc'.
    pose proof HMB1 as (_ & _ & _ & _ & _ & _ & Mw1 & _ & _ & _ & Md1).
    clear Hfr H0 Htc Md Mw.
    run_fp 100%nat [0x13cfc%Z] noscr false.
    call_getidx (tc - 1)%Z H0' Htc' Htags Md1 Mw1.
    destruct (getidx_frame _ _ HMB1 HP1 Hfr) as [HMB2 HP2].
    lazymatch goal with |- runs_to _ (@mkst _ ?R' _ _ _) _ =>
      apply phaseA2; [ | exact HP2];
      split; [creg (2%bv:reg)|];
      split; [lift_id H64i HR;
              lazymatch type of HR with regs_ok ?E ?sr _ =>
              lazymatch type of H64i with id (regs_ok _ ?sr0 _) =>
                exact (regs_same_on E sr0 sr regs R' [3; 4; 20; 21; 22; 23; 24; 25; 26; 27]%bv H64i HR ltac:(vm_compute; reflexivity)) end end
             | exact HMB2 ] end.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Theorem fuzz_runs : runs_to SEGS (mkst (FP:=FPI) regs (Z_to_bv 64 0x12f88) mem rom) Q.
  Proof.
    touch.
    pose proof (u64_range sp) as Hspr. pose proof (u64_range data) as Hdr.
    pose proof writable0 as HW. pose proof HW as (W1 & W2 & W3 & W4).
    pose proof gfool0 as [HG [gw Hgw]]. pose proof HG as (G1 & G2 & G3 & G4). pose proof data_ok0 as HD.
    pose proof (writable_rodata_apart_Ub mem _ _ 0x103ec 0x10490 ltac:(lia) ltac:(lia) ltac:(lia) HW Hro) as Hsro.
    unfold cell in Hgw.
    set (E := Env (vals_ev (junk_vals regs ++ fjunk_vals (fp_regs (FPState:=FPI)) ++ [Z_to_bv 64 n; gw])) (blobs_ev [bs])).
    assert (HR : regs_ok E (sr_vars 0) regs) by exact (regs_ok_vars [] regs _ (blobs_ev [bs])).
    assert (HF : fregs_ok E (sfr_vars 32) (fp_regs (FPState:=FPI))) by exact (fregs_ok_vars (junk_vals regs) (fp_regs (FPState:=FPI)) _ (blobs_ev [bs])).
    pose proof (HR : id _) as HR0.
    assert (HK : know_ok SEGS E mem
      [KAlign (EVar 2) 16; KRange (EVar 2) 1824 140737488355328; KRange (EVar 10) 1 140737488355328;
       KRange (EVar 64) 0 67108864; KWord (SA (ELit 0) 0x31400) 4 (EVar 65);
       KWr (SA (EVar 2) (-1824)) 1824; KWr (SA (ELit 0) 0x31400) 4;
       KDisj (SA (EVar 2) (-1824)) 1824 (SA (ELit 0) 0x31400) 4]).
    { constructor; [apply kalign_intro; [lia | cbn [edenot]; ev_simpl E; rewrite Hsp; exact Hal]|].
      constructor; [apply krange_intro; cbn [edenot]; ev_simpl E; rewrite Hsp; lia|].
      constructor; [apply krange_intro; cbn [edenot]; ev_simpl E; rewrite Ha0; lia|].
      constructor; [apply krange_intro; cbn [edenot]; ev_simpl E; rewrite u_small by lia; lia|].
      constructor; [eapply (kword_intro SEGS E mem (ELit 0) (Z_to_bv 64 0) 0x31400 4 (EVar 65) gw);
                    [reflexivity | cbn [edenot]; ev_simpl E; reflexivity | lia | lia
                    | rewrite u_small by lia; lia | rewrite u_small by lia; cbn; lia
                    | rewrite u_small by lia; exact Hgw]|].
      constructor; [apply (kwr_intro SEGS E mem (EVar 2) sp (-1824) 1824);
                    [cbn [edenot]; ev_simpl E; exact Hsp | lia | lia | lia |
                     replace (bv_unsigned sp + -1824)%Z with (bv_unsigned sp - 1824)%Z by lia; exact W4]|].
      constructor; [apply (kwr_intro SEGS E mem (ELit 0) (Z_to_bv 64 0) 0x31400 4 eq_refl);
                    rewrite ?u_small by lia; cbn [Z.add]; try lia; exact G4|].
      constructor; [cbn [kentry_ok]; unfold estart; cbn [a_base a_off edenot]; ev_simpl E; rewrite Hsp; rewrite u_small by lia; lia|].
      constructor. }
    (* [comment removed for export] *)
    run_fp 100%nat [0x13e4c%Z] noscr true.
    lazymatch goal with |- runs_to _ (@mkst _ _ _ ?M0 _) _ =>
      assert (HFRA : frame_mod mem M0 [(Z_to_bv 64 (s - 1824), 1824%Z)])
        by (rewrite EQM; frame_of_log [(SA (EVar 2) (-1824), 1824%Z)] ltac:(rewrite_getr)) end.
    kcell_auto HK (EVar 2) (-1040)%Z 4%nat HQ0. kcell_auto HK (EVar 2) (-1036)%Z 4%nat HQ1.
    (* [comment removed for export] *)
    lazymatch goal with |- runs_to _ (@mkst ?I ?R' _ ?M' _) _ =>
      eapply rt_call;
      [ eapply (Hparse data n bs (Z_to_bv 64 (s - 1056)) (Z_to_bv 64 (s - 1040)) (Z_to_bv 64 (s - 1016)) I R' M' rom _);
        [ regv HR (1%bv:reg); reflexivity
        | apply ret_ok_even; rewrite u_small by lia; reflexivity
        | unfold parse_pre; cbv zeta; cbn [t_parse_d t_ro_lo t_ro_hi tags_infoub]; rewrite !u_small by lia ]
      | cbv beta ] end.
    { split; [regv HR (2%bv:reg); rewrite_getr; rewrite ?alu_add_lit; f_equal; lia|].
      split; [regv HR (10%bv:reg); rewrite_getr; reflexivity|].
      split; [regv HR (11%bv:reg); rewrite_getr; reflexivity|].
      split; [regv HR (12%bv:reg); rewrite_getr; rewrite ?alu_add_lit; f_equal; lia|].
      split; [regv HR (13%bv:reg); reflexivity|].
      split; [regv HR (14%bv:reg); rewrite_getr; rewrite ?alu_add_lit; f_equal; lia|].
      split; [eapply data_ok_frame; [exact HFRA | exact HD | solve_apart]|].
      split; [split; [mlia|]; unfold cell; replace (s - 1040)%Z with (s + -1040)%Z by lia; exact HQ0|].
      split; [split; [mlia|]; unfold cell; replace (s - 1040 + 4)%Z with (s + -1036)%Z by lia; exact HQ1|].
      split; [mlia|]. split; [mlia|]. split; [mlia|].
      split; [eapply writable_frame; [exact HFRA|]; eapply (writable_sub _ _ _ _ _ _ HW); lia|].
      split; [mlia|]. split; [mlia|]. split; [mlia|].
      split; [eapply writable_frame; [exact HFRA|]; eapply (writable_sub _ _ _ _ _ _ HW); lia|].
      split; [eapply rodata_clear_frame; [exact HFRA | exact Hro | lia | lia | solve_apart]|].
      lia. }
    intros FPI' R' M1 (Hkeep & Hfkeep & Hpost).
    unfold parse_post in Hpost. cbv zeta in Hpost. cbn [t_parse_d tags_infoub] in Hpost.
    destruct Hpost as (Hfr & r & Hr10 & Hr01 & Hpr).
    unfold regs_kept in Hkeep. clear Hfkeep. after_call Hkeep FPI'. clear Hkeep.
    know_frame HK Hfr [(SA (EVar 2) (-1728), 672%Z); (SA (EVar 2) (-1016), 976%Z)].
    { rewrite Hsp; unfold v_addi; rewrite ?u_small by lia; repeat f_equal; lia. }
    rewrite u_small in Hfr by lia. rewrite u_small in Hpr by lia.
    assert (HF2 : frame_mod mem M1 BIG).
    { eapply frame_mod_trans_same.
      - eapply frame_mod_in2l; [| |exact HFRA]; rewrite ?u_small by lia; lia.
      - eapply frame_mod_incl; [|exact Hfr]. intros b m [Hb|[Hb|[]]]; injection Hb as <- <-;
          (exists (Z_to_bv 64 (s - 1824)), 1824%Z; split; [left; reflexivity| rewrite !u_small by lia; lia]). }
    kcell_auto HK (EVar 2) (-8)%Z 8%nat M1c. kcell_auto HK (EVar 2) (-16)%Z 8%nat M2c.
    kcell_auto HK (EVar 2) (-24)%Z 8%nat M3c. kcell_auto HK (EVar 2) (-32)%Z 8%nat M4c.
    kcell_auto HK (EVar 2) (-40)%Z 8%nat M5c.
    kcell_auto HK (ELit 0) 0x31400%Z 4%nat MG. rewrite u_small in MG by lia.
    apply (phaseA1 _ _ _ r); [| exact Hr10 | exact Hr01 | exact Hpr].
    split; [creg (2%bv:reg)|].
    split; [unfold id in HR0;
            lazymatch type of HR with regs_ok (Env (vals_ev ?V) _) ?sr _ => lift_to HR0 V;
              exact (regs_same_on _ _ sr regs _ [3; 4; 20; 21; 22; 23; 24; 25; 26; 27]%bv HR0 HR ltac:(vm_compute; reflexivity)) end|].
    unfold LibFuzzUbA.MEMB, cell64, cell.
    split; [replace (s - 8)%Z with (s + -8)%Z by lia; exact M1c|].
    split; [replace (s - 16)%Z with (s + -16)%Z by lia; exact M2c|].
    split; [replace (s - 24)%Z with (s + -24)%Z by lia; exact M3c|].
    split; [replace (s - 32)%Z with (s + -32)%Z by lia; exact M4c|].
    split; [replace (s - 40)%Z with (s + -40)%Z by lia; exact M5c|].
    split; [exact HF2|].
    split; [eapply writable_frame; [exact HF2 | exact HW]|].
    split; [eapply writable_frame; [exact HF2 | exact HG]|].
    split; [eexists; exact MG|].
    split; [eapply rodata_clear_frame; [exact HF2 | exact Hro | lia | lia | solve_apart]|].
    eapply data_ok_frame; [exact HF2 | exact HD | solve_apart].
  Qed.

End Proof.

Theorem fuzz_Ub_ok :
  parse_contract SEGS tags_infoub -> getidx_contract SEGS tags_infoub -> rte_contract SEGS 0x131b8 ->
  fuzz_contract SEGS infoub_abi.
Proof.
  intros Hparse Hgetidx Hrte.
  unfold fuzz_contract. cbn [fa_entry fa_gfool fa_depth fa_ro_lo fa_ro_hi infoub_abi].
  intros FPI regs mem rom ret sp data n bs Hra Hret Hsp Ha0 Ha1 Hn Hbs Hal Hdal Hsplo Hsphi Hd0 Hdhi Hblob Hstk Hout Hgfw Hgfr Hro Hdj1 Hdj2 Hdj3.
  destruct (fuzz_runs Hparse Hgetidx Hrte FPI regs mem rom ret sp data n bs Hra Hret Hsp Ha0 Ha1 Hn Hbs Hal Hsplo Hsphi Hd0 Hdhi
              Hblob Hstk Hgfw Hgfr Hro Hdj1 Hdj2 Hdj3) as (st' & Hsteps & FPI' & regs' & mem' & -> & Ha & Hk & Hf).
  exists FPI', regs', mem'. split; [exact Hsteps|]. split; [exact Ha|]. split; [exact Hk|]. exact Hf.
Qed.
