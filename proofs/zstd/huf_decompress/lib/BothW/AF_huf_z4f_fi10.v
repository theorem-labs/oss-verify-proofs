From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk RunConst Image Frame.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import PropExec MState Mem Cells Exec Step.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require SysStep.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXMem KXTac KXGo KXPost KXFoot KXGoF KXChk KXGoM.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF Shadow StepF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg RtCells ABase.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AF_huf_x2t_hdefs AF_huf_z4f_defs.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.


Lemma z4f10_img_ap : forall E X B O k L,
  0 <= O -> O + 64 <= 2^64 -> 1 <= L <= 8 ->
  0 <= bv_unsigned (edenot E B) + k -> bv_unsigned (edenot E B) + k + L <= 2^64 ->
  bv_unsigned (edenot E B) + k + L <= O \/ O + 64 <= bv_unsigned (edenot E B) + k ->
  flat E (SA (EAlu ALU_SRL X (ELit 58)) O) (elenZ E (ELit 1)) /\ flat E (SA B k) (elenZ E (ELit L)) /\
  (estart E (SA (EAlu ALU_SRL X (ELit 58)) O) + elenZ E (ELit 1) <= estart E (SA B k) \/
   estart E (SA B k) + elenZ E (ELit L) <= estart E (SA (EAlu ALU_SRL X (ELit 58)) O)).
Proof.
  intros E X B O k L HO1 HO2 HL HB1 HB2 HAP.
  pose proof (bv_unsigned_in_range _ (edenot E X)) as [RX0 RX1]. change (bv_modulus 64) with (2 ^ 64) in RX1.
  unfold flat, estart, elenZ. cbn [a_base a_off edenot].
  rewrite u_srl64, !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  change (58 mod 2 ^ 64) with 58. change (1 mod 2 ^ 64) with 1. change (2 ^ (58 mod 64)) with (2 ^ 58).
  rewrite (Z.mod_small L (2 ^ 64)) by lia.
  assert (HD : bv_unsigned (edenot E X) / 2 ^ 58 < 64)
    by (apply Z.div_lt_upper_bound; [lia | change (2 ^ 58 * 64) with (2 ^ 64); lia]).
  assert (HD0 : 0 <= bv_unsigned (edenot E X) / 2 ^ 58) by (apply Z.div_pos; lia).
  repeat split; lia.
Qed.

Lemma z4f10_brx : forall E X Y, bv_unsigned (edenot E X) <> bv_unsigned (edenot E Y) ->
  branch_taken BC_NE (edenot E (EAlu ALU_XOR (ELit 1) (EAlu ALU_SLTU (EAlu ALU_XOR X Y) (ELit 1)))) (edenot E (ELit 0)) = true.
Proof.
  intros E X Y H.
  pose proof (bv_unsigned_in_range _ (edenot E X)) as [RX _]. pose proof (bv_unsigned_in_range _ (edenot E Y)) as [RY _].
  cbn [edenot branch_taken].
  rewrite bv_eqb_Z, u_xor64, u_sltu64, u_xor64.
  change (bv_unsigned (Z_to_bv 64 1)) with 1. change (bv_unsigned (Z_to_bv 64 0)) with 0.
  assert (HL : 0 < Z.lxor (bv_unsigned (edenot E X)) (bv_unsigned (edenot E Y))).
  { assert (0 <= Z.lxor (bv_unsigned (edenot E X)) (bv_unsigned (edenot E Y)))
      by (apply Z.lxor_nonneg; split; intros; lia).
    assert (Z.lxor (bv_unsigned (edenot E X)) (bv_unsigned (edenot E Y)) <> 0)
      by (intros HE; apply H; apply Z.lxor_eq; exact HE).
    lia. }
  destruct (Z.ltb_spec (Z.lxor (bv_unsigned (edenot E X)) (bv_unsigned (edenot E Y))) 1); [lia|].
  reflexivity.
Qed.

Ltac z4fimg :=
  lazymatch goal with
  | |- flat ?E (SA (EAlu ALU_SRL ?X (ELit 58)) ?O) _ /\ flat ?E (SA ?B ?k) (elenZ _ (ELit ?L)) /\ _ =>
      apply (z4f10_img_ap E X B O k L);
      [ lia | lia | lia | z4fez; z4fnum; lia | z4fez; z4fnum; lia | z4fez; z4fnum; unfold AIMG_HI in *; lia ]
  end.

Section CANSEC1. Context {rc : runConstT}.
Section X42E.
  Variables (RNG : footprint).
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : amem).
  Variables (SPV DST dcap SRC n DT DTB tl lo : Z) (src dtb : list byte).
  Hypothesis CTX : x42e_ctx SPV DST dcap SRC n DT DTB tl lo src dtb.
  Hypothesis X2OK : huf_x2_ok dtb tl.
  Hypothesis NBOK : huf_nb_ok true dtb tl.
  Hypothesis ACTX : x42e_actx RNG m0 SPV DST dcap SRC n DT DTB lo.

  Variable POST : machine_state -> Prop.
  Hypothesis TL11 : tl = 11.
  Hypothesis FI11 : x42e_fi11_stmt RNG gp tp F fc m0 SPV DST dcap SRC n DT src dtb POST.
  Notation z4fI := (AF_huf_z4f_defs.z4fI m0 SPV DST dcap SRC DT src dtb).

  Lemma x42e_fi10 : x42e_fi10_stmt RNG gp tp F fc m0 SPV DST dcap SRC n DT src dtb POST.
  Proof using CTX X2OK NBOK ACTX TL11 FI11.
    pose proof CTX as CTX'. x42e_ctx_open CTX'. pose proof ACTX as ACTX'. x42e_actx_open ACTX'.
    unfold x42e_fi10_stmt.
    intros r mb mm q OL nd l1 l2 l3 i0 i1 i2 i3 o0 o1 o2 o3 u0 u1 u2 u3 j0 j1 ix c0 c1 c2 c3 e0 e1 e2 e3 av0 av1 av2 av3 av4 av5 av6 av7 av8 av9 av10 av11
      x1 x6 x18 x19 x25 x30
      w0 w1 w2
      MU WM MU0 WM0 MI OUT DTBb FR AR LC SRCB HND HR HOL HO0 HO1 HO2 HO3 HE0 HE1 HE2 HE3 HQ3 HQ0 HOLR HI0 HI1 HI2 HI3 HN0 HN1 HN2 HN3 HL1 HL2 HL3 HLN
      HU0 HU1 HU2 HU3 HJ0 HJ1 HIX HLBc0 HLBc1 HLBc2 HLBc3 KH KO. subst nd.

    destruct R1 as (R1a & R1b & R1c). destruct R2 as (R2a & R2b & R2c). destruct R3 as (R3a & R3b).
    assert (KF : 0 < dcap) by lia.
    assert (DTB8 : 8196 <= DTB) by (rewrite TL11 in DTBF; cbn in DTBF; lia).
    specialize (UDST KF). specialize (RDST KF). specialize (RDSTS KF).
    assert (TF : ztab_fact bsegs mm (DT + 4) 8192 4 [(2, 0, 11); (3, 1, 2)]) by (eapply x42f_tab; eassumption).
    assert (UQ : unpoisoned mm SRC (SRC + n) /\ unpoisoned mm DT (DT + DTB) /\ (0 < dcap -> unpoisoned mm DST (DST + dcap)))
      by (eapply x42f_unp; eassumption).
    destruct UQ as (USm & UDTm & UDSTm). specialize (UDSTm KF).
    assert (WRS : forall A k, DST <= A -> A + k <= DST + dcap -> 0 <= k -> wr_at bsegs mm A k)
      by (intros A k ? ? ?; destruct OUT as (OL0 & OH0 & OS); unfold wr_at; split; [lia|]; split; [lia|];
          intros i Hi; apply (OS (A + i)); lia).
    assert (WA3 : wr_at bsegs mm (DST + u3) 2) by (apply WRS; lia).
    assert (RW3 : rng RNG (DST + u3) 2) by (apply (rng_sub RNG DST dcap); [exact RDST | lia | lia]).
    clear WRS.
    pose proof (bv_unsigned_in_range _ c1) as RGc1. pose proof (bv_unsigned_in_range _ c2) as RGc2.
    pose proof (bv_unsigned_in_range _ c0) as RGc0. pose proof (bv_unsigned_in_range _ c3) as RGc3.
    change (bv_modulus 64) with (2 ^ 64) in RGc0, RGc1, RGc2, RGc3.
    unfold shspan in RDTS, RDSTS, RSRCS.
    set (ND := 2^64 - DT - 5).
    replace (Z_to_bv 64 (-1 * DT + -5)) with (Z_to_bv 64 ND) by (apply bv_eq; rewrite !Z_to_bv_unsigned; unfold ND, bv_wrap, bv_modulus; Z.div_mod_to_equations; lia).
    assert (NDR : 2^64 - 2^47 <= ND <= 2^64 - 4101) by (unfold ND; lia).
    assert (NDE : Z_to_bv 64 ND = Z_to_bv 64 (-1 * DT + -5)) by (apply bv_eq; rewrite !Z_to_bv_unsigned; unfold ND, bv_wrap, bv_modulus; Z.div_mod_to_equations; lia).
    clearbody ND.
    pose proof (lbw_pos _ _ HLBc2) as HC2. pose proof (DHI KF) as DHIk.
    lazymatch goal with |- evtF _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?tb) _ _ _ _ _) _ _ _ _ _ _) =>
      assert (TBF : ztab_fact bsegs mm tb 64 1 [(0, 0, 63)]) by (apply ztab_fact_img; [exact MI | lia | vm_compute; reflexivity])
    end.
    lazymatch type of TBF with ztab_fact _ _ ?tb _ _ _ =>
    kx_runFmd [549916] 120%nat [true]
      [KZRange DT 4096 (2^47); KZRange (DT + DTB) 4096 (2^47); KZAlign DT 4; KZRange ND (2^64 - 2^47) (2^64 - 4101);
       KZRange ix 0 2047; KZAlign (4 * ix) 4;
       KZRange DST 4096 (2^47); KZRange dcap 1 (2^47); KZRange u3 0 (2^47); KZRange (DST + u3) 4096 (2^47);
       KZRange (DST + dcap - (DST + u3)) 2 (2^47);
       KZRange SPV 4096 (2^47); KZRange SRC 4096 (2^47); KZRange n 8 (2^32); KZRange i2 7 (2^32); KZRange (n - i2) 8 (2^32);
       KZRange (bv_unsigned c2) 1 (2^64 - 1);
       KZTab (DT + 4) 8192 4 [(2, 0, 11); (3, 1, 2)]; KZTab tb 64 1 [(0, 0, 63)]; KZImg tb (tb + 64);
       KZWr (DST + u3) 2; KZWr (SPV + -232) 128;
       KZDisj (DST + u3) 2 (DT + 4) 8192; KZDisj (SPV + -232) 128 (DT + 4) 8192;
       KZDisj (DST + u3) 2 SRC n; KZDisj (SPV + -232) 128 SRC n]
      [(DT + 4, 8192); (SRC, n); (tb, 64)] [(DST + u3, 2); (SPV + -232, 128)] [(DT + 4, 8192); (DST + u3, 2); (SRC, n)]
    end.
    all: try z4fimg.
    all: try (lazymatch goal with |- accP _ _ ({| a_base := EAlu ALU_ADD (EMd M_MUL (ELit 4) _) _ |}, _) => z4facc RDT end).
    all: try (lazymatch goal with |- accP _ _ ({| a_base := EAlu ALU_SRL _ (ELit 58) |}, _) =>
      unfold accP, adenot; cbn [a_base a_off fst snd]; unfold PropExec.v_addi; apply (proj2 (proj2 RI));
      lazymatch goal with |- context [bv_unsigned (edenot ?E (EAlu ALU_SRL ?X (ELit 58)))] =>
        assert (HS : bv_unsigned (edenot E (EAlu ALU_SRL X (ELit 58))) < 64)
          by (pose proof (bv_unsigned_in_range _ (edenot E X)) as [R0 R1]; change (bv_modulus 64) with (2 ^ 64) in R1;
              cbn [edenot] in R0, R1 |- *; rewrite u_srl64, Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 64) with (2 ^ 64);
              change (2 ^ ((58 mod 2 ^ 64) mod 64)) with (2 ^ 58);
              apply Z.div_lt_upper_bound; [lia | change (2 ^ 58 * 64) with (2 ^ 64); lia]);
        pose proof (bv_unsigned_in_range _ (edenot E (EAlu ALU_SRL X (ELit 58)))) as [HS0 _];
        set (v := bv_unsigned (edenot E (EAlu ALU_SRL X (ELit 58)))) in *; clearbody v
      end;
      rewrite Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 64) with (2 ^ 64);
      rewrite Z.mod_small by (clear - HS HS0; lia); clear - HS HS0; lia end).
    all: try (lazymatch goal with |- branch_taken BC_NE _ _ = true =>
      apply z4f10_brx; kx_erange R38 (EVar 38); cbn [edenot] in R38; z4fez;
      repeat match goal with |- context [2 ^ ?e] => lazymatch e with context [_ mod _] => let v := eval vm_compute in e in change e with v end end;
      rewrite ?(Z.mod_small (bv_unsigned (ev KXE 38)) (2 ^ 64)) by lia;
      assert (D38 : bv_unsigned (ev KXE 38) / 2 ^ 3 < 8) by (apply Z.div_lt_upper_bound; lia);
      z4fnum; lia end).
    kx_post_regs_keep.
    kx_erange R35 (EVar 35). kx_erange R36 (EVar 36). kx_erange R38 (EVar 38).
     (lazymatch goal with |- context [mem_denot ?E _ _] => cbn [mem_denot]; z4fan E end).
     (lazymatch goal with FRh : rw_cells _ mm (SPV + -528) ?fr, ARh : rw_cells _ mm (SPV + -384) ?ar, LCh : rw_cells _ mm (SPV + -232) ?cs |- _ =>
      assert (I0 : z4fI mb mm fr ar cs) by (unfold z4fI; z4fsplit 12%nat; first [eassumption | reflexivity]) end).
     (lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?M _) => z4fmem M end).
    lazymatch goal with I0 : z4fI _ ?M ?fr ?ar ?cs |- _ =>
      destruct I0 as (MU' & WM' & MU0' & WM0' & MI' & STK' & DTB' & SRC' & FR' & AR' & LC' & LFR' & LAR') end.
    rewrite ?Z_to_bv_bv_unsigned in *.
    lazymatch goal with |- evtF _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?x30 _) _ _ _ _ _ _) =>
      assert (LBC3 : LBW 52 x30) by (lazymatch goal with |- LBW _ (edenot (kE ?zv ?xs) _) => e42_lb_chain (kE_atoms zv xs) end)
    end.

    cbn [edenot] in R35, R36, R38.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?M _) => set (mm1 := M) in *; clearbody mm1 end.
    repeat match goal with |- context [edenot (kE ?zv ?xs) ?e] => let v := fresh "kv" in set (v := edenot (kE zv xs) e) in *; clearbody v end.
    lazymatch goal with |- context [ev (kE ?zv ?xs) 38] => set (w38 := ev (kE zv xs) 38) in *; clearbody w38 end.
    lazymatch goal with |- context [ev (kE ?zv ?xs) 37] => set (w37 := ev (kE zv xs) 37) in *; clearbody w37 end.
    lazymatch goal with |- context [bv_unsigned (ev (kE ?zv ?xs) 36)] =>
      set (b36 := bv_unsigned (ev (kE zv xs) 36)) in *; clearbody b36 end.
    try lazymatch goal with H : context [bv_unsigned (ev (kE ?zv ?xs) 35)] |- _ =>
      set (b35 := bv_unsigned (ev (kE zv xs) 35)) in *; clearbody b35 end.
    clearbody KXxs.
    repeat match goal with
    | H : know_ok _ _ _ _ |- _ => clear H | H : log_flat _ _ |- _ => clear H | H : regs_ok _ _ _ |- _ => clear H
    | H : Forall _ _ |- _ => clear H | H : forall j, (j < length _)%nat -> ev _ j = _ |- _ => clear H end.
    change (2 ^ (3 mod 64)) with 8 in *.
    rewrite ?(Z.mod_small (bv_unsigned w38) (2 ^ 64)) in * by lia.
    assert (NBR : 0 <= bv_unsigned w38 / 8 <= 7) by (split; [apply Z.div_pos; lia | apply Z.lt_succ_r, Z.div_lt_upper_bound; lia]).
    set (nb := bv_unsigned w38 / 8) in *; clearbody nb.
    assert (UQ1 : unpoisoned mm1 SRC (SRC + n) /\ unpoisoned mm1 DT (DT + DTB) /\ (0 < dcap -> unpoisoned mm1 DST (DST + dcap)))
      by (eapply x42f_unp; eassumption).
    destruct UQ1 as (USm1 & _ & _).
    assert (M1nb : -1 * nb = - nb) by lia. rewrite ?M1nb in *. clear M1nb.
    assert (J2R : i2 - 7 <= i2 + - nb <= i2) by lia.
    set (j2 := i2 + - nb) in *; clearbody j2.
    kx_runFm [550064] 60%nat
      [KZRange SPV 4096 (2^47); KZRange SRC 4096 (2^47); KZRange n 8 (2^32); KZRange i2 7 (2^32); KZRange (n - i2) 8 (2^32);
       KZRange j2 0 (2^32); KZRange (n - j2) 8 (2^32); KZWr (SPV + -232) 128; KZDisj (SPV + -232) 128 SRC n]
      [(SRC, n)] [(SPV + -232, 128)] [(SRC, n)].
    all: try (z4facc RSRC).
    kx_post_regs_keep.
    lazymatch goal with |- context [mem_denot ?E _ _] => cbn [mem_denot]; z4fan E end.
    lazymatch goal with FRh : rw_cells _ mm1 (SPV + -528) ?fr, ARh : rw_cells _ mm1 (SPV + -384) ?ar, LCh : rw_cells _ mm1 (SPV + -232) ?cs |- _ =>
      assert (I1 : z4fI mb mm1 fr ar cs) by (unfold z4fI; z4fsplit 12%nat; first [eassumption | reflexivity]) end.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?M _) => z4fmem M end.
    lazymatch goal with I1 : z4fI _ ?M ?fr ?ar ?cs |- _ =>
      destruct I1 as (MU'' & WM'' & MU0'' & WM0'' & MI'' & STK'' & DTB'' & SRC'' & FR'' & AR'' & LC'' & LFR'' & LAR'') end.
    rewrite ?NDE.
    rewrite ?Z_to_bv_bv_unsigned in *.
    eapply (FI11 r mb _ q OL (-1 * DT + -5) l1 l2 l3 i0 i1 i2 i3 o0 o1 o2 o3 u0 u1 u2 _ j0 j1 j2 _ c0 c1 _ _ e0 e1 e2 e3
              av0 av1 av2 av3 av4 av5 av6 av7 av8 av9 av10 av11 _ _ _ _ _ _ w0 w1 w2).
    all: try eassumption.
    all: try reflexivity.
    1: (clear - R36 HU3; lia).
    1: (pose proof (bv_unsigned_in_range _ kv3) as RGk3; change (bv_modulus 64) with (2 ^ 64) in RGk3;
        change (2 ^ (53 mod 64)) with (2 ^ 53); rewrite (Z.mod_small (bv_unsigned kv3) (2 ^ 64)) by (clear - RGk3; lia);
        pose proof (z4f_div_rng (bv_unsigned kv3) 53 ltac:(clear - RGk3; lia) ltac:(lia)) as DV0;
        change (2 ^ (64 - 53)) with 2048 in DV0; clear - DV0; lia).
    1: e42_lb_reload.
  Qed.

End X42E.
End CANSEC1.
