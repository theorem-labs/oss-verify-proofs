(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import Image ZBridge SysStep ITree Nodes Decode Arr FP Tac InitMem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Common Require Import DrvAgree.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Spec Require Import Prelim Monad STree AsanCtrl AsanEmbed HarnessP ProgA AsanProgDeps SjStage1 SjS1Bytes.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.LibA Require Import ExecF ITreeA SysStepF.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AsanW Require Import AImg RtCells AProto ABase AMalloc_iface I_asan_memset AU_rt AH_memcpy0.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AsanW Require Import AU_kit AU_iface AHarnessU_iface AU_client_kit AU_fuzz_kit AU_parts_iface AU_steptac Stdio_kit.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.LibA Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.LibA Require Import StepF.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AsanW Require Import ShadowTac APC_kit APC_kit2 APC_kit3 APC_kit4 APC_docalloc APC_setcap APC_setdepth APC_active APC_create APC_dtor APC_memcmp APC_s12iface.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegP2A Require Import A2Lib.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AsanW Require Import APC_pid0.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AsanW Require Import APC_pid_t2.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib Require Import ADkModel.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AsanW Require Import APC_mpres.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import LiaTier0U.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac acc_hint ::= acc_hint_shadow.
Local Ltac solve_load ::= first [ solve_load_tight | solve_load_image ].
Local Ltac solve_store ::= solve_store_tight.


(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= lia_tier0u.
Local Ltac tlia ::= tlia_u.
Local Ltac lia3 ::= lia3_u.
Section CANSEC1. Context {rc : runConstT}.
Section S.
Variable AI : AMallocIface.
Notation CI := (aci AI).
Variable rng_fs : alayout -> footprint -> Prop.

Section T1.
  Hypothesis ONTA : opnew_nt_stmtA AI.
  Hypothesis ODA : opdelete_arr_stmtA AI.
  Hypothesis IMG_CI : forall iv, In iv client_ranges -> In iv CI.
  Hypothesis PARSE : parse_stmtA AI rng_fs.
  Hypothesis RFSM : forall L R R', fp_le R R' -> rng_fs L R -> rng_fs L R'.
  Variable (L : alayout).
  Variable (RNG : footprint).
  Variable (ra sp gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word).
  Variable (F : bvmap 5 word).
  Variable (fc : bv 32).
  Variable (m : amem).
  Variable (s : APS).
  Variable (LB : list ablock).
  Variable (lo : Z).
  Variable (rstk : region).
  Variable (data : list Z).
  Variable (D P R : Z).
  Variable (jr : list byte).
  Variable (trR : list Z).
  Variable (LBK : boxed (∀ b : ablock, In b LB → (∃ (p : AsanCtrl.aptr) (A n : Z), b = HB p A n) ∨ ∃ cls FA FN : Z, b = {| ab_kind := ABFake cls; ab_addr := FA; ab_size := FN |} ∧ cls ≠ 5 ∧ cls ≠ 4)).
  Variable (PAY : boxed (payload_atA LB D data)).
  Variable (DAT : bytes_at asegs m D (map (Z_to_bv 8) data)).
  Variable (DB : Forall (λ c : Z, 0 <= c < 256) data).
  Variable (D16 : D mod 16 = 0).
  Let len : Z := zlength data.
  Variable (DL : len < 2 ^ 26).
  Variable (CI0 : client_img m).
  Variable (CSH : client_sh m).
  Variable (fcls FA FN : Z).
  Variable (INF : In {| ab_kind := ABFake fcls; ab_addr := FA; ab_size := FN |} LB).
  Variable (FKH : FA <= P).
  Variable (FK2 : P + 80 <= FA + FN).
  Variable (FKB : ablk FA (FA + FN)).
  Variable (RP : P + 80 <= R).
  Variable (R8 : R mod 8 = 0).
  Variable (P8 : P mod 8 = 0).
  Variable (RPR : rng RNG R 24).
  Variable (RPP : rng RNG P 80).
  Variable (RSHR : boxed (rng RNG (R ≫ 3 + 2147450880) ((R + 24) ≫ 3 + 2147450880 - (R ≫ 3 + 2147450880)))).
  Variable (RSHP : boxed (rng RNG (P ≫ 3 + 2147450880) ((P + 80) ≫ 3 + 2147450880 - (P ≫ 3 + 2147450880)))).
  Variable (RSPR : bv_unsigned sp + 16 <= R).
  Variable (RHI : R + 24 <= r_hi rstk).
  Variable (R47 : R + 24 <= 2 ^ 47).
  Variable (LOA : ATOP + 4096 <= lo).
  Variable (LOS : lo <= bv_unsigned sp - (112 + (32 + (416 + 8192)))).
  Variable (RCL : rclean m rstk).
  Variable (RCL1 : r_lo rstk <= lo).
  Variable (RCL2 : bv_unsigned sp <= r_hi rstk).
  Variable (RCL3 : ATOP <= r_rlo rstk).
  Variable (RRNG : boxed (rrng RNG rstk)).
  Variable (STOP : bv_unsigned sp + 16 < al_top L).
  Variable (SP16 : bv_unsigned sp mod 16 = 0).
  Variable (m0 : amem).
  Variable (FZ : frm0 fc).
  Variable (TP : tp = Z_to_bv 64 ATP).
  Variable (HUL : HU L).
  Variable (UCR : boxed (uchain m (al_top L) AFREE_PC (bv_unsigned sp - 112) R (Nat.pred UDEPTH) trR)).
  Variable (TRR : (length trR <= 27)%nat).
  Variable (PRO : boxed (rw_cells asegs m R [CB 24 jr])).
  Variable (RSTK : rng RNG lo (al_top L - lo)).
  Variable (RI : rng_aimg RNG).
  Variable (RISH : boxed (rng_aimg_sh RNG)).
  Variable (RFS : rng_fs L RNG).
  Variable (AOK : aps_ok L s).
  Variable (RSP : 0 <= bv_unsigned sp < 2 ^ 64).
  Variable (H : 140735332483072 <= ATOP <= 140737479966720).
  Variable (FK1 : FA <= R).
  Variable (FKB1 : 6705152 <= FA).
  Variable (FKB2 : 0 <= FA).
  Variable (FKB3 : FA + FN <= ATOP).
  Variable (FKB4 : FA + FN + 8 <= 2 ^ 47).
  Variable (bF : Z).
  Variable (bFr : 0 <= bF <= 1).
  Variable (bFhi : FA + FN <= 2147446784 + bF * 140737479966720).
  Variable (bFlo : 17594333495296 * bF <= FA).
  Variable (LY1 : al_bot L + 8388608 = al_top L).
  Variable (LY2 : al_top L mod 4096 = 0).
  Variable (LY3 : al_top L <= 2 ^ 47).
  Variable (LEN0 : 0 <= len).
  Variable (CAPR : 32 <= CAP len < 2 ^ 26 + 32).
  Variable (PR0 : 0 <= R).
  Variable (FKB5 : AIMG_HI <= FA).
  Variable (FKB6 : 0 <= FA).
  Variable (FKB7 : FA + FN <= ATOP).
  Variable (FKB8 : FA + FN + 8 <= 2 ^ 47).
  Variable (SB : 2147450880 <= (P + 8) ≫ 3 + 2147450880 ∧ (P + 8) ≫ 3 + 2147450880 + 1 <= 17594333495296).
  Variable (SB0 : 2147450880 <= (P + 24) ≫ 3 + 2147450880 ∧ (P + 24) ≫ 3 + 2147450880 + 1 <= 17594333495296).
  Variable (SB1 : 2147450880 <= (P + 32) ≫ 3 + 2147450880 ∧ (P + 32) ≫ 3 + 2147450880 + 1 <= 17594333495296).
  Variable (SB2 : 2147450880 <= (P + 40) ≫ 3 + 2147450880 ∧ (P + 40) ≫ 3 + 2147450880 + 1 <= 17594333495296).
  Variable (SB3 : 2147450880 <= (P + 48) ≫ 3 + 2147450880 ∧ (P + 48) ≫ 3 + 2147450880 + 1 <= 17594333495296).
  Variable (SB4 : 2147450880 <= (P + 56) ≫ 3 + 2147450880 ∧ (P + 56) ≫ 3 + 2147450880 + 1 <= 17594333495296).
  Variable (SB5 : 2147450880 <= (P + 64) ≫ 3 + 2147450880 ∧ (P + 64) ≫ 3 + 2147450880 + 1 <= 17594333495296).
  Variable (SB6 : 2147450880 <= (P + 72) ≫ 3 + 2147450880 ∧ (P + 72) ≫ 3 + 2147450880 + 1 <= 17594333495296).
  Variable (SB7 : 2147450880 <= R ≫ 3 + 2147450880 ∧ R ≫ 3 + 2147450880 + 1 <= 17594333495296).
  Variable (SB8 : 2147450880 <= (R + 8) ≫ 3 + 2147450880 ∧ (R + 8) ≫ 3 + 2147450880 + 1 <= 17594333495296).
  Variable (SB9 : 2147450880 <= (R + 16) ≫ 3 + 2147450880 ∧ (R + 16) ≫ 3 + 2147450880 + 1 <= 17594333495296).
  Variable (RS : rng RNG ((P + 8) ≫ 3 + 2147450880) 1).
  Variable (RS0 : rng RNG ((P + 24) ≫ 3 + 2147450880) 1).
  Variable (RS1 : rng RNG ((P + 32) ≫ 3 + 2147450880) 1).
  Variable (RS2 : rng RNG ((P + 40) ≫ 3 + 2147450880) 1).
  Variable (RS3 : rng RNG ((P + 48) ≫ 3 + 2147450880) 1).
  Variable (RS4 : boxed (rng RNG ((P + 56) ≫ 3 + 2147450880) 1)).
  Variable (RS5 : boxed (rng RNG ((P + 64) ≫ 3 + 2147450880) 1)).
  Variable (RS6 : boxed (rng RNG ((P + 72) ≫ 3 + 2147450880) 1)).
  Variable (RS7 : boxed (rng RNG (R ≫ 3 + 2147450880) 1)).
  Variable (RS8 : boxed (rng RNG ((R + 8) ≫ 3 + 2147450880) 1)).
  Variable (RS9 : boxed (rng RNG ((R + 16) ≫ 3 + 2147450880) 1)).
  Variable (junk : list byte).
  Variable (K1 : CAP len <= 4294967295).
  Variable (K2 : 0 < CAP len).
  Variable (psb ptp : AsanCtrl.aptr).
  Variable (s1' : APS).
  Variable (RNG1 : footprint).
  Variable (FPL1 : fp_le RNG RNG1).
  Variable (u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 : word).
  Variable (m2 : amem).
  Variable (MI2 : mem_inv asegs m2).
  Variable (ST2 : stk asegs m2 lo (bv_unsigned sp + -112)).
  Variable (ARS1 : aps_rest s1' = aps_rest s).
  Variable (SBA TPA : Z).
  Variable (jsb jtp : list byte).
  Variable (BRS : ablock_range SBA (SB_BYTES len)).
  Variable (BRT : ablock_range TPA (TAPE_BYTES len)).
  Variable (AH2 : AHEAP AI L RNG1 (aps_m s1') (HB ptp TPA (TAPE_BYTES len) :: HB psb SBA (SB_BYTES len) :: LB) m2).
  Variable (BLKS : rw_cells asegs m2 SBA [CB (Z.to_nat (SB_BYTES len)) jsb]).
  Variable (BLKT : rw_cells asegs m2 TPA [CB (Z.to_nat (TAPE_BYTES len)) jtp]).
  Variable (DOC2 : rw_cells asegs m2 (P + 24) [C8 (Z_to_bv 64 TPA); C8 (Z_to_bv 64 SBA); C8 (Z_to_bv 64 (CAP len))]).
  Variable (PIM : rw_cells asegs m2 (P + 8) [C8 (Z_to_bv 64 0)]).
  Variable (PMAX : rw_cells asegs m2 (P + 48) [C8 (Z_to_bv 64 4294967295); C1 (Z_to_bv 8 0)]).
  Variable (PCP : rw_cells asegs m2 (P + 64) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]).
  Variable (PR : rw_cells asegs m2 R [CB 24 jr]).
  Variable (SC : rw_cells asegs m2 ((P + 8) ≫ 3 + 2147450880) [C1 (Z_to_bv 8 0)]).
  Variable (SC0 : rw_cells asegs m2 ((P + 24) ≫ 3 + 2147450880) [C1 (Z_to_bv 8 0)]).
  Variable (SC1 : rw_cells asegs m2 ((P + 32) ≫ 3 + 2147450880) [C1 (Z_to_bv 8 0)]).
  Variable (SC2 : rw_cells asegs m2 ((P + 40) ≫ 3 + 2147450880) [C1 (Z_to_bv 8 0)]).
  Variable (SC3 : rw_cells asegs m2 ((P + 48) ≫ 3 + 2147450880) [C1 (Z_to_bv 8 0)]).
  Variable (SC4 : rw_cells asegs m2 ((P + 56) ≫ 3 + 2147450880) [C1 (Z_to_bv 8 0)]).
  Variable (SC5 : rw_cells asegs m2 ((P + 64) ≫ 3 + 2147450880) [C1 (Z_to_bv 8 0)]).
  Variable (SC6 : rw_cells asegs m2 ((P + 72) ≫ 3 + 2147450880) [C1 (Z_to_bv 8 0)]).
  Variable (SC7 : rw_cells asegs m2 (R ≫ 3 + 2147450880) [C1 (Z_to_bv 8 0)]).
  Variable (SC8 : rw_cells asegs m2 ((R + 8) ≫ 3 + 2147450880) [C1 (Z_to_bv 8 0)]).
  Variable (SC9 : rw_cells asegs m2 ((R + 16) ≫ 3 + 2147450880) [C1 (Z_to_bv 8 0)]).
  Variable (FR : rw_cells asegs m2 (bv_unsigned sp + -112) [CB 8 (take 8 (take 16 (take 24 (take 32 (take 40 (take 48 (take 56 (take 64 (take 72 (take 80 (take 88 (take 96 (take 104 junk))))))))))))); C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  Variable (CST2 : client_static s LB m2).
  Variable (PW2 : aheap_pres_W CI LB (bv_unsigned sp) (apid_W P R) m m2).
  Variable (AFR1 : AFRESH (aps_m s1')).
  Variable (DK1 : dk (aps_m s1') < DWMAX).
  Lemma apid_t1 :
    implMA RNG1 (ii <- impl_create amalloc_M (new_handlerA AAllocAsan) len;; lb <- padded_alloc amalloc_M (new_handlerA AAllocAsan) len;; match lb with | Some _ => parse_impl amalloc_M afree_M (new_handlerA AAllocAsan) data | None => mret () end;;; mret ((psb, ptp).1, (psb, ptp).2, ii, lb)) s1' (apid_post AI L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB len lo P R m) (MS (mkR (Z_to_bv 64 614072) (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp u0 u1 u2 (Z_to_bv 64 R) s1 (Z_to_bv 64 0) u3 u4 u5 u6 u7 u8 u9 (Z_to_bv 64 len) (Z_to_bv 64 D) (Z_to_bv 64 (P + 8)) (Z_to_bv 64 P) (Z_to_bv 64 1) s7 (Z_to_bv 64 (CAP len)) (Z_to_bv 64 (P + 24)) (Z_to_bv 64 2147450880) (Z_to_bv 64 ((P + 8) ≫ 3 + 2147450880)) u10 u11 u12 u13) F (Z_to_bv 64 614072) fc None m2 (seg_rom asegs)).

  Proof using All.
    (* [comment removed for export] *)
    clear BLKS BLKT jsb jtp.
    (* [comment removed for export] *)
    pose proof (rng_fp_le _ _ _ _ FPL1 RSTK) as RSTK1. pose proof (rng_fp_le _ _ _ _ FPL1 RI) as RI1.
    unbox RISH. pose proof (rng_fp_le _ _ _ _ FPL1 RISH) as RISH1. pose proof (rng_fp_le _ _ _ _ FPL1 RPR) as RPR1. pose proof (rng_fp_le _ _ _ _ FPL1 RPP) as RPP1.
    clear RSTK RI RISH RPR RPP.
    apply implMA_from_evtF.
    (* [comment removed for export] *)
    unbox RS. pose proof (rng_fp_le _ _ _ _ FPL1 RS) as RS_8. clear RS.
    park_memA m2. unfold parkedA in SC, PIM.
    boxm RSTK1. boxm RI1. boxm RISH1.
    Time steps_to 0x9735c.
    unbox RSTK1. unbox RI1. unbox RISH1.
    Time eapply evtF_cut.
    { eapply aactive_proof with (lo := lo); rewrite ?unsigned_lit by lia;
        first [exact ST2 | exact MI2 | (destruct CST2 as [_ X]; exact X) | (unfold AACTIVE_STACK; lia) | exact RI1
              | (eapply rng_sub'; [exact RSTK1| lia]) | lia]. }
    cbv beta. intros ms2 (v0 & v1 & v2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m3 & -> & MI3 & ST3 & MU3 & WM3 & CS13).
    rewrite ?unsigned_lit in ST3, MU3 by lia. retlit. unfold client_wr in MU3.
    unparkA.
    Time trmB MU3 WM3.
    Time lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (AH3 : AHEAP AI L RNG1 (aps_m s1') (HB ptp TPA (TAPE_BYTES len) :: HB psb SBA (SB_BYTES len) :: LB) mx)
        by (eapply (AI_frame AI); [exact AH2| exact MU3| exact WM3|];
            apply Forall_cons; [left; left; cbn; lia|];
            repeat (apply Forall_cons; [apply (aclient_range_cr AI IMG_CI); vm_compute; reflexivity|]); apply Forall_nil)
    end.
    clear AH2.
    (* [comment removed for export] *)
    Time assert (PW3 : aheap_pres_W CI LB (bv_unsigned sp) (apid_W P R) m m3).
    { eapply aheap_pres_W_trans; [exact PW2|]. eapply aheap_pres_W_of_munch; [exact MU3| exact WM3|].
      intros a Ha Hc Hx. unfold apid_W, client_wr in Hx. cbn [app outside] in Hx |- *.
      pose proof (aclient_lo_or_sp AI _ _ _ _ _ _ _ a AH3 (fun b Hb => or_intror (or_intror Hb)) Hc) as Ha'. lia. }
    clear PW2.
    assert (FWF : Forall wfar2 (apid_W P R)).
    { unfold apid_W, client_wr, wfar2. cbn [app]. repeat (apply Forall_cons; [cbn [fst snd]; unfold KLS in *; lia|]). apply Forall_nil. }
    Time pose proof (client_img_W AI IMG_CI _ _ _ _ _ _ _ _ _ CI0 PW3 FWF AH3 MI3) as CI3.
    pose proof (client_sh_W AI IMG_CI _ _ _ _ _ CSH PW3 FWF) as CSH3.
    park_memA m3.
    pose proof CI3 as (_ & VTI3 & _ & _). unfold AVTAB_IMPL, vtab_impl_cells in VTI3.
    pose proof CS13 as (SA1 & _ & SA3 & _). unfold AACTIVE, AFALLBACK, fallback_cells, AFALLBACK_VT, AFALLBACK_NAME, AFALLBACK_DESC, w0 in SA1, SA3.
    pose proof (client_sh_cell m3 0x642200 CSH3 ltac:(cbn; tauto)) as SHA. pose proof (client_sh_cell m3 0x6422a0 CSH3 ltac:(cbn; tauto)) as SHF.
    pose proof (client_sh_cell m3 0x103ea8 CSH3 ltac:(cbn; tauto)) as SHV.
    change (Z.shiftr 0x642200 3 + 2147450880) with 2148271168 in SHA. change (Z.shiftr 0x6422a0 3 + 2147450880) with 2148271188 in SHF.
    change (Z.shiftr 0x103ea8 3 + 2147450880) with 2147583957 in SHV.
    (* [comment removed for export] *)
    unfold AACTIVE.
    boxm RSTK1. boxm RPR1. boxm RPP1. boxm RS_8.
    Time steps_to 0x973cc.
    unbox RSTK1. unbox RPR1. unbox RPP1. unbox RS_8.
    lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?q) _ _ _ _) => idtac "PC" q; constr_eq q 0x973cc end.
    apply evtF_done.
    clear SHA SHF SHV VTI3 SA1 SA3.
    pose proof (HU_in _ _ HUL (or_introl eq_refl)) as HUM.
    eapply implMA_bind.
    { eapply implMA_leaves; [| exact (impl_create_dk len s1')].
      pose proof (acreate_proof AI IMG_CI ONTA) as CR. unfold acreate_stmt in CR.
      Time (eapply CR with (lo := lo) (DST := P + 8) (len := len); try reflexivity; rewrite ?unsigned_lit by lia;
        first [exact AH3 | exact MI3 | exact ST3 | exact TP | exact HUM | exact RI1 | exact RISH1 | exact PIM
              | (unfold ACREATE_STACK, ASETCAP_STACK, OPNEW_NT_STACK_A, OPNEW_STACK_A, AMALLOC_STACK; lia)
              | exact CI3 | exact CSH3
              | (exists fcls, FA, FN; split; [right; right; exact INF| split; [lia| split; [lia| exact FKB]]])
              | (unfold shc, shx, ASHOFF; exact SC) | (unfold shx, ASHOFF; exact RS_8)
              | (eapply rng_sub'; [exact RPR1| lia]) | (eapply rng_sub'; [exact RPP1| lia]) | (eapply rng_sub'; [exact RSTK1| lia])
              | (eapply aps_ok_rest; [exact ARS1| exact AOK]) | lia]). }
    cbv beta. intros [[[pim psi] poc] pia] s2' RNG2 ms3
      [(FPL2 & w0' & w1 & w2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & w3 & w4 & w5 & w6 & m4 & -> & MI4 & ST4 & HPX4 & ARS2 & RR4) DKS2].
    destruct DKS2 as (DF2 & _ & _). destruct (DF2 AFR1) as [AFR2 DKB2]. assert (DK2 : dk (aps_m s2') < DWMAX) by (clear - DK1 DKB2; lia). clear DF2 DKB2.
    destruct RR4 as (AIM & ASI & AOC & AIA & p1 & p2 & pad & jsi & joc & jia & BRM & BRI & BRO & BRA & AH4 & DST4 & OBJ4 & IDX4 & OC4 & IA4).
    rewrite ?unsigned_lit in ST4, HPX4 by lia. retlit.
    clear IDX4 OC4 IA4 jsi joc jia. unfold aimpl_cells in OBJ4.
    (* [comment removed for export] *)
    assert (INF1 : In (mkABlock (ABFake fcls) FA FN) (HB ptp TPA (TAPE_BYTES len) :: HB psb SBA (SB_BYTES len) :: LB)) by (right; right; exact INF).
    unparkA. clear PIM.
    Time trxC HPX4 INF1 IMG_CI ltac:(fun _ => clear - LOA LOS FK2 FKB3 FKB2 FK1 FKH RP RSPR R47 PR0 R8 P8 RSP STOP LY3 bFr bFhi bFlo SB SB0 SB1 SB2 SB3 SB4 SB5 SB6 SB7 SB8 SB9).
    assert (PW4 : aheap_pres_W CI LB (bv_unsigned sp) (apid_W P R) m m4).
    { eapply aheap_pres_W_trans; [exact PW3|]. eapply pres_W_of_x; [exact HPX4| lia| intros b Hb; right; right; exact Hb|].
      intros a Hc Ho Hx. unfold apid_W in Ho. cbn [app outside] in Ho. lia. }
    clear PW3.
    pose proof (client_static1_pres_x AI IMG_CI _ _ _ _ _ _ HPX4 ltac:(eapply wfar_ablk; [exact FKB| lia| lia]) CS13) as CS14.
    clear CS13 HPX4 INF1 AH3 CI3 CSH3 MU3 WM3.
    pose proof (rng_fp_le _ _ _ _ FPL2 RSTK1) as RSTK2. pose proof (rng_fp_le _ _ _ _ FPL2 RI1) as RI2.
    pose proof (rng_fp_le _ _ _ _ FPL2 RISH1) as RISH2. pose proof (rng_fp_le _ _ _ _ FPL2 RPR1) as RPR2. pose proof (rng_fp_le _ _ _ _ FPL2 RPP1) as RPP2.
    pose proof (rng_fp_le _ _ _ _ FPL2 RS_8) as RS_8'. clear RSTK1 RI1 RISH1 RPR1 RPP1 RS_8. rename RS_8' into RS_8.
    unbox RS5. pose proof (rng_fp_le _ _ _ _ (fp_le_trans _ _ _ FPL1 FPL2) RS5) as RS_64. clear RS5.
    (* [comment removed for export] *)
    apply implMA_from_evtF.
    pose proof (munch_refl [(lo, bv_unsigned sp)] m4) as MU5. pose proof (wmono_refl asegs m4) as WM5.
    park_memA m4. unfold parkedA in SC5, PCP, FR.
    boxm RI2. boxm RISH2.
    Time steps_to 0x95e3c.
    unbox RI2. unbox RISH2.
    unparkA.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) => remember mx as m5 eqn:EM5 end. clear EM5.
    pose proof (ablock_range_lin _ _ BRM) as (BRM1 & BRM2 & BRM3 & BRM4). pose proof (ablock_range_lin _ _ BRI) as (BRI1 & BRI2 & BRI3 & BRI4).
    pose proof (ablock_range_lin _ _ BRO) as (BRO1 & BRO2 & BRO3 & BRO4). pose proof (ablock_range_lin _ _ BRA) as (BRA1 & BRA2 & BRA3 & BRA4).
    pose proof (ablock_range_lin _ _ BRS) as (BRS1 & BRS2 & BRS3 & BRS4). pose proof (ablock_range_lin _ _ BRT) as (BRT1 & BRT2 & BRT3 & BRT4).
    unfold IMPL_BYTES, OC_BYTES, ISARR_BYTES, MAX_DEPTH in *.
    Time trmC MU5 WM5 ltac:(fun _ => clear - LOA LOS FK2 FKB3 FKB2 FKH RP RSPR R47 PR0 BRS3 BRT3 BRM3 BRI3 BRO3 BRA3 BRS2 BRT2 BRM2 BRI2 BRO2 BRA2
                                      SB SB0 SB1 SB2 SB3 SB4 SB5 SB6 SB7 SB8 SB9).
    assert (AH5 : AHEAP AI L RNG2 (aps_m s2') (HB pia AIA 1024 :: HB poc AOC (8 * 1024) :: HB psi ASI (SIDX_BYTES len) :: HB pim AIM 96
                                                :: HB ptp TPA (TAPE_BYTES len) :: HB psb SBA (SB_BYTES len) :: LB) m5)
      by (eapply (AI_frame AI); [exact AH4| exact MU5| exact WM5| apply Forall_cons; [left; left; cbn; lia| apply Forall_nil]]).
    assert (PW5 : aheap_pres_W CI LB (bv_unsigned sp) (apid_W P R) m m5).
    { eapply aheap_pres_W_trans; [exact PW4|]. eapply aheap_pres_W_of_munch; [exact MU5| exact WM5|].
      intros a Ha Hc Hx. cbn [outside] in Hx |- *.
      pose proof (aclient_lo_or_sp AI _ _ _ _ _ _ _ a AH5 (fun b Hb => or_intror (or_intror (or_intror (or_intror (or_intror (or_intror Hb)))))) Hc) as Ha'. lia. }
    pose proof (client_static1_munch32 _ _ _ CS14 MU5 WM5 ltac:(apply Forall_cons; [apply wfar_high; lia| apply Forall_nil])) as CS15.
    pose proof (fp_le_trans _ _ _ FPL1 FPL2) as FPL12. assert (ARS12 : aps_rest s2' = aps_rest s) by (rewrite ARS2; exact ARS1).
    clear MU5 WM5 AH4 PW4 CS14 FPL1 FPL2 ARS1 ARS2 CST2 MI2 ST2.
    drop_mem m3. drop_mem m2. drop_mem m4. try clear m1. try clear m0.
    try clear v0. try clear v1. try clear v2. try clear v3. try clear v4. try clear v5. try clear v6.
    try clear c1. try clear c2. try clear c3. try clear c4. try clear c5. try clear c6. try clear c7.
    try clear u0. try clear u1. try clear u2. try clear u3. try clear u4. try clear u5. try clear u6. try clear u7. try clear u8. try clear u9.
    try clear u10. try clear u11. try clear u12. try clear u13. try clear s1'. try clear RNG1.
    clear FKB5 FKB6 FKB7 FKB8.
    exact (apid_t2 AI rng_fs ONTA ODA IMG_CI PARSE RFSM L RNG ra sp gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB lo rstk data D P R jr trR LBK PAY DAT DB D16
       DL CI0 CSH fcls FA FN INF FKH FK2 FKB RP R8 P8 RSHR RSHP RSPR RHI R47 LOA LOS RCL RCL1 RCL2 RCL3 RRNG STOP SP16 FZ TP HUL UCR TRR PRO RFS AOK RSP H FK1 FKB1
       FKB2 FKB3 FKB4 bF bFr bFhi bFlo LY1 LY2 LY3 LEN0 CAPR PR0 SB SB0 SB1 SB2 SB3 SB4 SB5 SB6 SB7 SB8 SB9 RS0 RS1 RS2 RS3 RS4 RS6 RS7 RS8 RS9 junk K1 K2
       psb ptp SBA TPA BRS BRT FWF HUM pim psi poc pia s2' RNG2 w0' w1 w2 d1 d2 d3 d4 d5 d6 d7 w3 w4 w5 w6 m5 MI4 ST4 AIM ASI AOC AIA p1 p2 pad BRM BRI
       BRO BRA PCP SC5 RSTK2 RI2 RISH2 RPR2 RPP2 RS_8 RS_64 FR BRM1 BRM2 BRM3 BRM4 BRI1 BRI2 BRI3 BRI4 BRO1 BRO2 BRO3 BRO4 BRA1 BRA2 BRA3 BRA4 BRS1 BRS2 BRS3
       BRS4 BRT1 BRT2 BRT3 BRT4 SC9 SC8 SC7 SC6 SC4 SC3 SC2 SC1 SC0 SC PR PMAX DOC2 OBJ4 DST4 AH5 PW5 CS15 FPL12 ARS12 AFR2 DK2).
  Qed.
End T1.
End S.
End CANSEC1.
