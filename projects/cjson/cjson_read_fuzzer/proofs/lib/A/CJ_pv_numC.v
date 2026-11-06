(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Bytes Arr.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require Import LBase LSCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require LiaOn.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.LiaOn.SepM.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import CJ_bandM.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_skipws.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_skipws.CJ_band2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_pwlopts_A.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_pwlopts_A.CJ_band3.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import AImg RT_defs CJ_iface AShadow CJ_tree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_phex4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_phex4.CJ_pbuf.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import CJ_conv.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_phex4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_phex4.CJ_parse_lemmas.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import CJ_pvalue_lemmas.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_pv_ctx.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_pv_ctx.CJ_fp_lemmas.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_fuzz_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_fuzz_iface.CJ_print_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require ICPT_pcsdefs.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_pcsdefs.CJ_print_lemmas.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require ICPT_pcsdefs.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_pcsdefs.CJ_print_lemmas2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import CJ_pv_ctx CJ_pv_common CJ_pv_cases CJ_pv_calls CJ_pv_lits CJ_pv_numK ICPT_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_pstrA.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_pstrA.CJ_shfast.
Local Ltac sh_resolve_if ::= sh_resolve_if_fast.
Local Ltac sh_join v Cv rdk ::= sh_join_fast v Cv rdk.
(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require StoreCache.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.StoreFast.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import StoreCache.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import LiaOn.
Local Ltac mem_after_store ::= mem_after_store_cached.
Local Ltac addr_eq_tac ::= addr_eq_tac_cached.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_cached segs m m' MU WM.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section NUMC.
  Variable Q : pvi.
  Local Notation AI := (q_ai Q).    Local Notation TI := (q_ti Q).
  Local Notation ra := (q_ra Q).    Local Notation sp := (q_sp Q).    Local Notation gp := (q_gp Q).    Local Notation tp := (q_tp Q).
  Local Notation s0 := (q_s0 Q).    Local Notation s1 := (q_s1 Q).    Local Notation s2 := (q_s2 Q).    Local Notation s3 := (q_s3 Q).
  Local Notation s4 := (q_s4 Q).    Local Notation s5 := (q_s5 Q).    Local Notation s6 := (q_s6 Q).    Local Notation s7 := (q_s7 Q).
  Local Notation s8 := (q_s8 Q).    Local Notation s9 := (q_s9 Q).    Local Notation s10 := (q_s10 Q).  Local Notation s11 := (q_s11 Q).
  Local Notation F := (q_F Q).      Local Notation m := (q_m Q).      Local Notation g := (q_g Q).
  Local Notation sp0 := (q_sp0 Q).  Local Notation SPB := (q_SPB Q).  Local Notation LR := (q_LR Q).    Local Notation B := (q_B Q).
  Local Notation LF := (q_LF Q).    Local Notation np0 := (q_np0 Q).  Local Notation BB := (q_BB Q).    Local Notation CH := (q_CH Q).
  Local Notation n := (q_n Q).      Local Notation p := (q_p Q).      Local Notation PB := (q_PB Q).    Local Notation len0 := (q_len0 Q).
  Local Notation dep := (q_dep Q).  Local Notation fw := (q_fw Q).    Local Notation lo := (q_lo Q).
  Local Notation SA := (q_SA Q).    Local Notation Fr := (q_Fr Q).
  Hypothesis PVL : pvl Q.
  Local Notation SP := (bv_unsigned sp).
  Local Notation POST := (pvalue_post AI TI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F sp0 SPB LR B LF np0 BB CH n p PB len0 dep fw lo m g).
  Ltac lits := pose proof (pvl_lits Q PVL)
                 as ((PL1 & PL2 & PL3) & PB8 & AL & S47 & TOP & BOT & PB80 & CEIL & LO & TP & N1 & BLR & DEPN & DEP0 & PNZ
                     & CHOK & CHL & CHB & RA1 & RA2 & NPM & BBA & LEN0 & LFR & (GSA1 & GSA2) & (FAL & FLO & FHI & FNEW)
                     & SPR & RAR & S0R & (TOPR & BOTE) & CHN0);
               pose proof (Z.shiftr_div_pow2 Fr 3 ltac:(lia)) as SHFR; change (2^3) with 8 in SHFR;
               pose proof alloc_ceiling_eq as ACE; pose proof KHIGH_eqs as KHE.
  Ltac dj := cbn [disjoint_from cells_size Cells.csize Nat.add length map]; rewrite ?cells_size_mapC8, ?cells_size_mapC1, ?length_map; unfold AERRNO, ATP; lia.
  Ltac steq := unfold CASE_ST, mkR, SHR; repeat (lazymatch goal with |- @eq Z _ _ => lia | |- _ => first [reflexivity | progress f_equal] end).
  Hypothesis ENS : ensure_stmt AI TI.
  Hypothesis FLAGLOW : art_flag_low_stmt AI.
  Hypothesis MEMSET : asan_memset_spec.
  Hypothesis MEMCPY : asan_memcpy_spec.
  Local Notation ASHBASE := CJ_pv_cases.ASHBASE.

  (* [comment removed for export] *)
  Lemma num_X : forall mm mo1 g1 LB1 TRS1 B1 np1 errv1 loc jb shp Fx fcx (r : Z)
      (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x27 x28 x29 x30 x31 : word),
    pv_exit Q mm mo1 g1 LB1 TRS1 B1 np1 errv1 loc jb shp Fx fcx r ->
    LSCPS asegs POST
      (MS (mkR x1 (Z_to_bv 64 SA) gp tp x5 x6 x7 sp (Z_to_bv 64 SA) (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17
              x18 x19 x20 x21 x22 x23 (Z_to_bv 64 Fr) (SHR Fr) (Z_to_bv 64 Fr) x27 x28 x29 x30 x31)
          Fx (Z_to_bv 64 0x84968) fcx None mm (seg_rom asegs)) mo1 g1.
  Proof.
    intros until x31. intros nelH_; (nelim nelH_ 10%nat; intros FRX HL ERR MI PVA CHN CC GM TV OUT). lits. bandM. sepM. unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in FLO. bandM. sepM. unfold SHR.
    (nelimp FRX 11%nat; intros SAVW LOC LL PAD ST HDR BODY SHC L16 FRM FA).
    pose proof (pv_out_LR Q _ _ _ _ _ OUT) as HLR.
    unfold SHCV, SHCW in SHC.
    destruct shp as [|b0 [|b1 [|b2 [|b3 [|b4 [|b5 [|b6 [|b7 [|b8 [|b9 [|b10 [|b11 [|b12 [|b13 [|b14 [|b15 [|? ?]]]]]]]]]]]]]]]]]; try (cbn in L16; (cut_to L16; (cut_to L16; lia))).
    cbn [map] in SHC. clear L16.
    pose proof (conj OUT ERR) as OUTB. clear OUT ERR.
    eapply lscps_step_evt. cbv beta delta [mkR].
    pose proof (munch_refl [(Z.shiftr Fr 3 + 2147450880, Z.shiftr Fr 3 + 2147450880 + 16)] mm) as MU.
    pose proof (wmono_refl asegs mm) as WM.
    zstep. do 5 sbstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
    assert (OWN : Forall (pv_own_iv Q) [(Z.shiftr Fr 3 + 2147450880, Z.shiftr Fr 3 + 2147450880 + 16)])
      by (constructor; [unfold pv_own_iv; cbn [fst snd]; lia| constructor]).
    zstep. apply evt_done. cbv beta.
    destruct OUTB as [OUT ERR].
    lazymatch goal with H : mem_inv asegs m2 |- _ => rename H into MI2 end.
    eapply (pv_epi' Q PVL FLAGLOW) with (shp := [b0; b1; b2; b3; -8; -8; -8; -8; b8; b9; b10; b11; -8; b13; b14; b15]).
    split.
    { unfold PVFR. split; [exact SAVW|]. split; [exact LOC|]. split; [exact LL|]. split; [exact PAD|]. split; [exact ST|].
      unfold FHDR, FBODY, SHCV, SHCW in *.
      split; [eapply (rw_cells_transport asegs); [exact HDR| exact MU| exact WM| rewrite ?SHFR; dj]|].
      split; [eapply (rw_cells_transport asegs); [exact BODY| exact MU| exact WM| rewrite ?SHFR; dj]|].
      split; [cbn [map]; exact SHC|]. split; [reflexivity|]. split; [exact FRM| exact FA]. }
    split; [eapply (pvm_art_store Q PVL); [exact HL| exact MU| exact WM| exact OWN]|].
    split; [eapply (rw_cells_transport asegs); [unfold AERRNO, ATP in ERR |- *; exact ERR| exact MU| exact WM| rewrite ?SHFR; dj]|].
    split; [exact MI2|].
    split; [eapply (pvm_agree_store Q PVL); [exact HL| exact HLR| exact MU| exact WM| exact OWN| exact PVA]|].
    split. { eapply cj_chain_frame; [exact CHN| exact MU| exact WM|]. intros A k Hin. cbn. split; [| exact I].
             (* [comment removed for export] *)
             pose proof (HLR _ (BLR _ Hin)) as INA. pose_blk_band HL INA. pose proof (frame1_sh_band Fr FAL ltac:(lia) FHI) as (FB1 & FB2). lia. }
    split; [eapply (pvm_chain_cells_store Q PVL); [exact CC| exact MU| exact OWN]|].
    split; [exact GM|]. split; [exact TV|].
    eapply (pv_out_ext Q); [exact OUT| exact MU| exact WM| cbn; rewrite ?SHFR; Z.div_mod_to_equations; lia|].
    intros A k Hin. cbn. split; [| exact I].
    pose_blk_band HL Hin. pose proof (frame1_sh_band Fr FAL ltac:(lia) FHI) as (FB1 & FB2). lia.   (* [comment removed for export] *)
  Qed.

  (* [comment removed for export] *)
  Lemma num_T : forall m0 mo1 g1 LB1 TRS1 B1 np1 errv1 buf len off bs0 loc j0 nb j1 j2 t j3 Fx fcx (r : Z) mm bs
      (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x20 x23 x28 x29 x30 x31 : word),
    NUMX Q dep m0 mo1 g1 LB1 TRS1 B1 np1 errv1 buf len buf len off bs0 loc j0 nb j1 j2 t j3 SHP_NUM Fx fcx ->
    0 <= r <= 25 -> off + r + 2 <= len ->
    munch [(buf + off, buf + off + r + 1)] m0 mm -> wmono asegs m0 mm -> mem_inv asegs mm ->
    u8arr asegs mm buf bs -> length bs = length bs0 ->
    LSCPS asegs POST
      (MS (mkR x1 (Z_to_bv 64 SA) gp tp x5 x6 x7 sp (Z_to_bv 64 SA) (Z_to_bv 64 (buf + off)) x11 x12 x13 x14 x15 x16 x17
              (Z_to_bv 64 46) (Z_to_bv 64 PB) x20 (Z_to_bv 64 r) (Z_to_bv 64 (Fr + 96)) x23 (Z_to_bv 64 Fr) (SHR Fr) (Z_to_bv 64 Fr) (Z_to_bv 64 ASHBASE) x28 x29 x30 x31)
          Fx (Z_to_bv 64 0x8492c) fcx None mm (seg_rom asegs)) mo1 g1.
  Proof.
    intros until x31. intros [CTX FRX] Hr ROOM MU WM MI ARR LBS. lits. bandM. sepM. unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in FLO. bandM. sepM. unfold SHR, CJ_pv_cases.ASHBASE.
    (nelimp CTX 13%nat; intros HL HP PBS1 ARR0 LEN PN ERR MI0 PVA CHN CC SSZ _).
    (nelimp FRX 16%nat; intros SAVW LOC LL PAD ST HDR P0 P1 P2 P3 P4 P5 SHC L16 FRM FA).
    (nelimp PN 3%nat; intros PN1 PN2 PN3).
    (nelimp (art_block_range AI _ _ _ _ _ _ _ _ _ _ _ HL (perm_in_head _ _ _ HP)) 4%nat; intros R1 R2 R3 R4). pose_perm_blk_band HL HP. unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in R1. bandM. sepM. try rewrite alloc_ceiling_eq in R4.
    pose proof (art_block_shadow_ok AI _ _ _ _ _ _ _ _ _ _ _ HL (perm_in_head _ _ _ HP)) as SOKB.
    (nelimp (art_frame_facts AI _ _ _ _ _ _ _ _ _ _ _ HL ltac:(left; reflexivity)) 8%nat; intros _ _ _ _ _ _ _ FD). change (fsz 1) with 128 in FD.
    pose proof (FD buf len (perm_in_head _ _ _ HP)) as FDB.
    (* [comment removed for export] *)
    clear SAVW LOC PAD ST HDR P0 P1 P2 P3 P4 P5 SHC ERR ARR0 PBS1.
    eapply lscps_step_evt. cbv beta delta [mkR].
    zstep. zstep. zstep.
    pose proof (shadow_ok_shchk1 m0 buf len (buf + off + r) SOKB ltac:(lia)) as CK. sepM. asan_chk CK.
    (* [comment removed for export] *)
    destruct (u8_store' mm buf bs (buf + off + r) (off + r) (wb 0) ARR ltac:(lia) ltac:(rewrite LBS; lia)) as [SOK ARR'].
    clear ARR. step.
    lazymatch goal with
    | |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m1 ?a ?bs) _) =>
        replace (write_to_mem m1 a bs) with (write_to_mem m1 (wa (buf + off + r)) [wb 0])
          by (f_equal; first [reflexivity| symmetry; apply le1_lit8; lia| unfold wa; f_equal; lia])
    end.
    store_done. rename ARR' into ARR.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mm2 end.
    lazymatch goal with H : mem_inv asegs mm2 |- _ => rename H into MI2 end.
    (* [comment removed for export] *)
    (nelimp CTX 8%nat; intros _ _ PBS1 _ _ _ ERR _).
    (nelimp FRX 14%nat; intros SAVW LOC _ PAD ST HDR P0 P1 P2 P3 P4 P5 SHC _).
    assert (CTX2 : PVM Q dep mm2 mo1 g1 LB1 TRS1 B1 np1 errv1 buf len off (upd bs (Z.to_nat (off + r)) (wb 0))).
    { eapply (pvm_wext Q PVL); [exact CTX| exact MU| exact WM| exact MI2| | | exact ARR| rewrite upd_length, LBS; reflexivity].
      - constructor; [unfold pv_wiv; cbn [fst snd]; lia| constructor].
      - eapply (rw_cells_transport asegs); [unfold AERRNO, ATP in ERR |- *; exact ERR| exact MU| exact WM| dj]. }
    assert (FRX2 : NFR Q mm2 loc j0 nb j1 j2 t j3 SHP_NUM Fx fcx).
    { eapply (nfr_wext Q PVL); [exact FRX| exact MU| exact WM| | | | | exact FRM| exact FA].
      - sepM. constructor; [unfold nf_wiv; cbn [fst snd]; unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG; try rewrite alloc_ceiling_eq; (lia_on Hr ROOM PL1 CEIL LO N1 GSA1 FLO FHI SPR PN1 R1 BR BMf0 SMf)| constructor].
      - eapply stk_transport_disjoint; [exact ST| exact MU| exact WM| dj].
      - eapply (rw_cells_transport asegs); [exact P1| exact MU| exact WM| dj].
      - eapply (rw_cells_transport asegs); [exact P4| exact MU| exact WM| dj]. }
    pose proof (rw_cells_transport asegs _ m0 mm2 _ _ PBS1 MU WM ltac:((cut_on [ROOM PL1 CEIL LO N1 GSA1 FLO SPR R1 BR] dj))) as PBS2. unfold PBS in PBS2.
    pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 CTX2)))))))))))) as SSZ2.
    clear MU WM CTX FRX SAVW LOC PAD ST HDR P0 P1 P2 P3 P4 P5 SHC ERR PBS1 ARR.
    zstep. zstep. zstep.
    pose proof (stack_shb0 mm2 (PB + 16) SSZ2 ltac:(lia)) as Z16. asan_chk Z16. clear Z16.
    pose proof (munch_refl [(PB, PB + 32)] mm2) as MU. pose proof (wmono_refl asegs mm2) as WM.
    zstep. zstep. zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mm3 end.
    lazymatch goal with H : mem_inv asegs mm3 |- _ => rename H into MI3 end.
    assert (CTX3 : PVM Q dep mm3 mo1 g1 LB1 TRS1 B1 np1 errv1 buf len (off + r) (upd bs (Z.to_nat (off + r)) (wb 0))).
    { eapply (pvm_off_store Q PVL); [exact CTX2| exact MU| exact WM| exact MI3| unfold PBS, wz; unfold wz in PBS2; exact PBS2| lia]. }
    assert (FRX3 : NFR Q mm3 loc j0 nb j1 j2 t j3 SHP_NUM Fx fcx).
    { (nelimp FRX2 12%nat; intros _ _ _ _ ST2 _ _ P12 _ _ P42 _).
      eapply (nfr_wext Q PVL); [exact FRX2| exact MU| exact WM| | | | | exact FRM| exact FA].
      - constructor; [unfold nf_wiv; cbn [fst snd]; lia| constructor].
      - eapply stk_transport_disjoint; [exact ST2| exact MU| exact WM| dj].
      - eapply (rw_cells_transport asegs); [exact P12| exact MU| exact WM| dj].
      - eapply (rw_cells_transport asegs); [exact P42| exact MU| exact WM| dj]. }
    zstep. apply evt_done. cbv beta.
    eapply num_X. eapply (pvx_exit1 Q PVL).
    - split; [exact CTX3| eapply (pvfr_of_nfr Q PVL); exact FRX3].
    - exists 0. split; [lia|]. split; [lia|]. rewrite Z.add_0_r. apply nth_error_upd_same. rewrite LBS. lia.
  Qed.

  (* [comment removed for export] *)
  Definition nloop_post (m0 : word -> option byte) (buf len off r : Z) (Fx : bvmap 5 word) (fcx : bv 32)
      (x1 x5 x6 x7 x23 x28 x29 x30 x31 : word) : machine_state -> Prop :=
    fun ms' => exists mm' bs' (x11' x12' x13' x14' x15' x16' x17' x20' : word),
      ms' = MS (mkR x1 (Z_to_bv 64 SA) gp tp x5 x6 x7 sp (Z_to_bv 64 SA) (Z_to_bv 64 (buf + off)) x11' x12' x13' x14' x15' x16' x17'
                    (Z_to_bv 64 46) (Z_to_bv 64 PB) x20' (Z_to_bv 64 r) (Z_to_bv 64 (Fr + 96)) x23 (Z_to_bv 64 Fr) (SHR Fr) (Z_to_bv 64 Fr) (Z_to_bv 64 ASHBASE) x28 x29 x30 x31)
               Fx (Z_to_bv 64 0x8492c) fcx None mm' (seg_rom asegs)
      /\ u8arr asegs mm' buf bs' /\ Z.of_nat (length bs') = len /\ mem_inv asegs mm'
      /\ munch [(buf + off, buf + off + r + 1)] m0 mm' /\ wmono asegs m0 mm'.

  Lemma num_loop : forall (m0 : word -> option byte) (buf len off r : Z) (nb : list byte) (Fx : bvmap 5 word) (fcx : bv 32)
      (x1 x5 x6 x7 x23 x28 x29 x30 x31 : word) (k : nat) (i : Z) (mm : word -> option byte) (bs : list byte)
      (x15 x16 x17 : word) (a1v a2v a3v a4v s4v : Z),
    a1v = buf + off + i -> a2v = Fr + 32 + i -> a3v = buf + off + i -> a4v = r - i -> s4v = Fr + 32 + i ->
    (Z.to_nat (r - i) <= k)%nat -> 0 <= i < r -> r <= 25 -> 0 <= off -> off + r + 2 <= len ->
    (AIMG_HI <= buf /\ sclr buf len) ->    (* [comment removed for export] *)
    buf + len <= alloc_ceiling -> (buf + len + 16 <= Fr \/ Fr + 128 <= buf - 16) ->
    shadow_ok m0 buf len -> (forall a, Fr + 32 <= a < Fr + 58 -> shchk m0 a 1) -> rw_cells asegs m0 (Fr + 32) [CB 26 nb] ->
    u8arr asegs mm buf bs -> Z.of_nat (length bs) = len -> mem_inv asegs mm ->
    munch [(buf + off, buf + off + r + 1)] m0 mm -> wmono asegs m0 mm ->
    evt asegs (nloop_post m0 buf len off r Fx fcx x1 x5 x6 x7 x23 x28 x29 x30 x31)
      (MS (mkR x1 (Z_to_bv 64 SA) gp tp x5 x6 x7 sp (Z_to_bv 64 SA) (Z_to_bv 64 (buf + off)) (Z_to_bv 64 a1v) (Z_to_bv 64 a2v) (Z_to_bv 64 a3v) (Z_to_bv 64 a4v) x15 x16 x17
              (Z_to_bv 64 46) (Z_to_bv 64 PB) (Z_to_bv 64 s4v) (Z_to_bv 64 r) (Z_to_bv 64 (Fr + 96)) x23 (Z_to_bv 64 Fr) (SHR Fr) (Z_to_bv 64 Fr) (Z_to_bv 64 ASHBASE) x28 x29 x30 x31)
          Fx (Z_to_bv 64 0x848c4) fcx None mm (seg_rom asegs)).
  Proof.
    intros until x31. intros k.
    induction k as [|k IH]; intros i mm bs x15 x16 x17 a1v a2v a3v a4v s4v -> -> -> -> -> Hk Hi Hr OFF ROOM BLO BHI FDB SOKB SCK NB0 ARR LEN MI MU WM; [exfalso; lia|].
    lits. bandM. sepM. unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in FLO, BLO. bandM. sepM. try rewrite alloc_ceiling_eq in BHI. unfold SHR, CJ_pv_cases.ASHBASE.
    (* [comment removed for export] *)
    assert (L26 : length nb = 26%nat) by (destruct NB0 as [[W _] _]; cbn in W; destruct W as [W _]; exact W).
    pose proof (u8arr_of_rw_cells _ _ _ _ _ (rw_cells_transport asegs _ m0 mm _ _ NB0 MU WM ltac:(dj))) as NB.
    destruct (nth_error nb (Z.to_nat i)) as [b|] eqn:Eb; [| exfalso; apply nth_error_None in Eb; lia].
    pose proof (u8arr_read _ mm (Fr + 32) nb i b (wa (Fr + 32 + i)) NB Eb ltac:(lia) eq_refl) as RD.
    pose proof (bv_unsigned_in_range 8 b) as BR. change (bv_modulus 8) with 256 in BR.
    (* [comment removed for export] *)
    assert (STORE : forall (v : Z) (x16' : word), 0 <= v < 256 ->
      evt asegs (nloop_post m0 buf len off r Fx fcx x1 x5 x6 x7 x23 x28 x29 x30 x31)
        (MS (mkR x1 (Z_to_bv 64 SA) gp tp x5 x6 x7 sp (Z_to_bv 64 SA) (Z_to_bv 64 (buf + off)) (Z_to_bv 64 (buf + off + i)) (Z_to_bv 64 (Fr + 32 + i)) (Z_to_bv 64 (buf + off + i)) (Z_to_bv 64 (r - i)) (Z_to_bv 64 v) x16' x17
                (Z_to_bv 64 46) (Z_to_bv 64 PB) (Z_to_bv 64 (Fr + 32 + i)) (Z_to_bv 64 r) (Z_to_bv 64 (Fr + 96)) x23 (Z_to_bv 64 Fr) (Z_to_bv 64 (Z.shiftr Fr 3 + 2147450880)) (Z_to_bv 64 Fr) (Z_to_bv 64 2147450880) x28 x29 x30 x31)
            Fx (Z_to_bv 64 0x848e0) fcx None mm (seg_rom asegs))).
    { intros v x16' Hv.
      zstep. zstep.
      pose proof (shadow_ok_shchk1 m0 buf len (buf + off + i) SOKB ltac:(lia)) as CK. sepM. asan_chk CK.
      destruct (u8_store' mm buf bs (buf + off + i) (off + i) (wb v) ARR ltac:(lia) ltac:(lia)) as [SOK ARR'].
      clear ARR. step.
      lazymatch goal with
      | |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m1 ?a ?bs1) _) =>
          replace (write_to_mem m1 a bs1) with (write_to_mem m1 (wa (buf + off + i)) [wb v])
            by (f_equal; first [reflexivity| symmetry; apply le1_lit8; lia| unfold wa; f_equal; lia])
      end.
      store_done. rename ARR' into ARR.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mm2 end.
      lazymatch goal with H : mem_inv asegs mm2 |- _ => rename H into MI2 end.
      zstep. zstep. zstep. zstep. zstep. zstep. if_cases Ke; zify_cond Ke.
      - (* [comment removed for export] *)
        eapply (IH (i + 1)); [lia| lia| lia| lia| lia| lia| lia| exact Hr| exact OFF| exact ROOM| unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG; lia| try rewrite alloc_ceiling_eq; lia| exact FDB
                             | exact SOKB| exact SCK| exact NB0| exact ARR| rewrite upd_length; exact LEN| exact MI2| exact MU| exact WM].
      - (* [comment removed for export] *)
        zstep. apply evt_done. unfold nloop_post. exists mm2, (upd bs (Z.to_nat (off + i)) (wb v)). nexists 8%nat.
        split; [unfold SHR, CJ_pv_cases.ASHBASE; reflexivity|].
        split; [exact ARR|]. split; [rewrite upd_length; exact LEN|]. split; [exact MI2|]. split; [exact MU| exact WM]. }
    (* [comment removed for export] *)
    zstep. zstep.
    pose proof (SCK (Fr + 32 + i) ltac:(lia)) as CKS. sepM. asan_chk CKS.
    step. zstep. if_cases Kd; zify_cond Kd.
    - apply STORE. lia.
    - zstep. apply STORE. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma num_J : forall m0 mo1 g1 LB1 TRS1 B1 np1 errv1 buf len off bs0 loc j0 nb j1 j2 t j3 Fx fcx (r : Z)
      (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x23 x28 x29 x30 x31 : word),
    NUMX Q dep m0 mo1 g1 LB1 TRS1 B1 np1 errv1 buf len buf len off bs0 loc j0 nb j1 j2 t j3 SHP_NUM Fx fcx ->
    0 <= r <= 25 -> off + r + 2 <= len ->
    LSCPS asegs POST
      (MS (mkR x1 (Z_to_bv 64 SA) gp tp x5 x6 x7 sp (Z_to_bv 64 SA) (Z_to_bv 64 (buf + off)) x11 x12 x13 x14 x15 x16 x17
              (Z_to_bv 64 46) (Z_to_bv 64 PB) (Z_to_bv 64 (Fr + 32)) (Z_to_bv 64 r) (Z_to_bv 64 (Fr + 96)) x23 (Z_to_bv 64 Fr) (SHR Fr) (Z_to_bv 64 Fr) (Z_to_bv 64 ASHBASE) x28 x29 x30 x31)
          Fx (Z_to_bv 64 0x848b0) fcx None m0 (seg_rom asegs)) mo1 g1.
  Proof.
    intros until x31. intros CTXX Hr ROOM. lits. bandM. sepM. unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in FLO. bandM. sepM. unfold SHR, CJ_pv_cases.ASHBASE.
    pose proof CTXX as [CTX FRX].
    (nelimp CTX 9%nat; intros HL HP PBS1 ARR0 LEN PN ERR MI0 _).
    (nelimp FRX 16%nat; intros SAVW LOC LL PAD ST HDR P0 P1 P2 P3 P4 P5 SHC L16 FRM FA).
    (nelimp PN 3%nat; intros PN1 PN2 PN3).
    (nelimp (art_block_range AI _ _ _ _ _ _ _ _ _ _ _ HL (perm_in_head _ _ _ HP)) 4%nat; intros R1 R2 R3 R4). pose_perm_blk_band HL HP. unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in R1. bandM. sepM. try rewrite alloc_ceiling_eq in R4.
    pose proof (art_block_shadow_ok AI _ _ _ _ _ _ _ _ _ _ _ HL (perm_in_head _ _ _ HP)) as SOKB.
    (nelimp (art_frame_facts AI _ _ _ _ _ _ _ _ _ _ _ HL ltac:(left; reflexivity)) 8%nat; intros _ _ _ _ _ _ _ FD). change (fsz 1) with 128 in FD.
    pose proof (FD buf len (perm_in_head _ _ _ HP)) as FDB.
    assert (SCK : forall a, Fr + 32 <= a < Fr + 58 -> shchk m0 a 1).
    { intros a Ha. eapply (num_shchk1 Q PVL); [exact SHC| exact L16| reflexivity| exact Ha]. }
    clear SAVW LOC PAD ST HDR P0 P2 P3 P4 P5 SHC ERR PBS1.
    eapply lscps_step_evt. cbv beta delta [mkR].
    zstep. if_cases K0; zify_cond K0.
    - (* [comment removed for export] *)
      apply evt_done. cbv beta.
      eapply (num_T m0 mo1 g1 LB1 TRS1 B1 np1 errv1 buf len off bs0 loc j0 nb j1 j2 t j3 Fx fcx r m0 bs0);
        [exact CTXX| exact Hr| exact ROOM| apply munch_refl| apply wmono_refl| exact MI0| exact ARR0| reflexivity].
    - zstep. zstep. zstep. zstep.
      eapply evt_cut.
      { eapply (num_loop m0 buf len off r nb Fx fcx x1 x5 x6 x7 x23 x28 x29 x30 x31 (Z.to_nat r) 0 m0 bs0);
          first [ exact SOKB | exact SCK | exact P1 | exact ARR0 | exact LEN | exact MI0 | apply munch_refl | apply wmono_refl | exact FDB
                | unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG; (lia_on Hr ROOM PL1 CEIL LO N1 GSA1 FLO SPR PN1 R1 K0 BMf0 BR) | try rewrite alloc_ceiling_eq; lia | lia ]. }
      cbv beta. intros ms' PO.
      (nelim PO 16%nat; intros mm' bs' x11' x12' x13' x14' x15' x16' x17' x20' -> ARR' LEN' MI' MU' WM').
      apply evt_done. cbv beta.
      eapply (num_T m0 mo1 g1 LB1 TRS1 B1 np1 errv1 buf len off bs0 loc j0 nb j1 j2 t j3 Fx fcx r mm' bs');
        [exact CTXX| exact Hr| exact ROOM| exact MU'| exact WM'| exact MI'| exact ARR'| lia].
  Qed.

  (* [comment removed for export] *)
  Lemma num_E : forall mm mo1 g1 LB1 TRS1 B1 np1 errv1 buf len off bs loc j0 nb j1 j2 t j3 Fx fcx (r : Z)
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x23 x28 x29 x30 x31 : word),
    NUMX Q dep mm mo1 g1 LB1 TRS1 B1 np1 errv1 buf len buf len off bs loc j0 nb j1 j2 t j3 SHP_NUM Fx fcx ->
    0 <= r <= 25 ->
    LSCPS asegs POST
      (MS (mkR x1 (Z_to_bv 64 SA) gp tp x5 x6 x7 sp (Z_to_bv 64 SA) x10 x11 x12 x13 x14 x15 x16 x17
              (Z_to_bv 64 46) (Z_to_bv 64 PB) (Z_to_bv 64 (Fr + 32)) (Z_to_bv 64 r) (Z_to_bv 64 (Fr + 96)) x23 (Z_to_bv 64 Fr) (SHR Fr) (Z_to_bv 64 Fr) (Z_to_bv 64 ASHBASE) x28 x29 x30 x31)
          Fx (Z_to_bv 64 0x848a0) fcx None mm (seg_rom asegs)) mo1 g1.
  Proof.
    intros until x31. intros [CTX FRX] Hr. lits. bandM. sepM. unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in FLO. bandM. sepM. unfold SHR, CJ_pv_cases.ASHBASE.
    (nelimp CTX 9%nat; intros HL HP PBS1 ARR0 LEN PN ERR MI0 _).
    (nelimp PN 3%nat; intros PN1 PN2 PN3).
    eapply lscps_step_evt. cbv beta delta [mkR].
    zstep. zstep. zstep.
    change (Z_to_bv 64 552016) with (wz AENSURE_ENTRY). apply evt_done. cbv beta.
    eapply lscps_bind.
    { eapply (pvx_ensure Q PVL ENS) with (needed := r + 1); [split; [exact CTX| eapply (pvfr_of_nfr Q PVL); exact FRX]| lia| rewrite unsigned_lit by lia; lia]. }
    cbv beta. intros ms2 mo2 g2 PO.
    (nelim PO 23%nat; intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2 LB2 TRS2 B2 np2 errv2 -> RES).
    replace (ret_pc (Z_to_bv 64 0x848ac)) with (Z_to_bv 64 0x848ac) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    destruct RES as [[-> EX] | (buf' & len' & bs' & -> & BNZ & [CTX2 FRX2] & ROOM & LEN2)].
    - (* [comment removed for export] *)
      pose proof EX as ((_ & _) & _ & _ & MI2 & _).
      eapply lscps_step_evt. cbv beta delta [mkR]. zstep. if_cases K; zify_cond K; [| exfalso; apply K; reflexivity].
      apply evt_done. cbv beta. eapply num_X. exact EX.
    - (nelimp CTX2 9%nat; intros HL2 HP2 _ _ _ _ _ MI2 _).
      (nelimp (art_block_range AI _ _ _ _ _ _ _ _ _ _ _ HL2 (perm_in_head _ _ _ HP2)) 4%nat; intros R1 _ _ R4). pose_perm_blk_band HL2 HP2. unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in R1. bandM. sepM. try rewrite alloc_ceiling_eq in R4.
      (nelim (nfr_of_pvfr Q _ _ _ _ _ _ FRX2) 8%nat; intros j0' nb' j1' j2' t' j3' FRX3 _).
      eapply lscps_step_evt. cbv beta delta [mkR]. zstep. if_cases K; zify_cond K; [exfalso; try rewrite Z.mod_small in K by lia; lia|].
      apply evt_done. cbv beta.
      eapply (num_J m2 mo2 g2 LB2 TRS2 B2 np2 errv2 buf' len' off bs' loc j0' nb' j1' j2' t' j3' Fx fcx r); [split; [exact CTX2| exact FRX3]| exact Hr| lia].
  Qed.

  (* [comment removed for export] *)
  Lemma num_L : forall mm mo1 g1 LB1 TRS1 B1 np1 errv1 buf len off bs loc j0 nb j1 j2 t j3 Fx fcx (r : Z)
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x23 x28 x29 x30 x31 : word),
    NUMX Q dep mm mo1 g1 LB1 TRS1 B1 np1 errv1 buf len buf len off bs loc j0 nb j1 j2 t j3 SHP_NUM Fx fcx ->
    0 <= r < 2^63 ->
    LSCPS asegs POST
      (MS (mkR x1 (Z_to_bv 64 SA) gp tp x5 x6 x7 sp (Z_to_bv 64 SA) x10 x11 x12 x13 x14 x15 x16 x17
              (Z_to_bv 64 46) (Z_to_bv 64 PB) (Z_to_bv 64 (Fr + 32)) (Z_to_bv 64 r) (Z_to_bv 64 (Fr + 96)) x23 (Z_to_bv 64 Fr) (SHR Fr) (Z_to_bv 64 Fr) (Z_to_bv 64 ASHBASE) x28 x29 x30 x31)
          Fx (Z_to_bv 64 0x84890) fcx None mm (seg_rom asegs)) mo1 g1.
  Proof.
    intros until x31. intros CTXX Hr. lits. bandM. sepM. unfold SHR, CJ_pv_cases.ASHBASE.
    pose proof CTXX as [CTX FRX]. (nelimp CTX 9%nat; intros _ _ _ _ _ _ _ MI0 _).
    eapply lscps_step_evt. cbv beta delta [mkR].
    zstep. zstep. if_cases K; zify_cond K.
    - (* [comment removed for export] *)
      apply evt_done. cbv beta. eapply num_E; [exact CTXX| lia].
    - zstep. zstep. apply evt_done. cbv beta.
      eapply num_X. eapply (pvx_exit0 Q PVL). split; [exact CTX| eapply (pvfr_of_nfr Q PVL); exact FRX].
  Qed.
End NUMC.


End CeilWrap.
