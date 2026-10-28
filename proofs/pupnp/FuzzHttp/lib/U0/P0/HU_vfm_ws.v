From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run Fs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge STRW_tac Image.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Spec Require Import StrFun StrFun2.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import Segs F_ctype H_scanner_get_token H_vfmatch_A.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Ceiling.
Import ListNotations.
Open Scope Z_scope.
Set Printing Width 1000.
Set Printing Depth 100.

Section VFW.
Context {HCEIL : HasCeiling}.

  Variables (q lo S MB A len cap cur0 : Z) (bs : list byte).
  Hypothesis VOK : vf_ok q lo S MB A len cap cur0 bs.

  Notation qq := (q + -208)%Z.
  Notation W0 := [(q - 304, q - 104); (S + 8, S + 16)]%Z.
  Notation dpost := (dpost q lo S MB A len cap cur0 bs).
  Notation linv := (linv q lo S MB A len cap bs).
  Notation headst := (headst q S cur0). Notation contst := (contst q S cur0). Notation exitst := (exitst q S cur0).
  Notation SCc := (SCc S MB). Notation MBc := (MBc MB A len cap). Notation BUFc := (BUFc A bs). Notation FX := (FX q).
  Notation F0 := (F0 q). Notation F36 := (F36 q). Notation F40 := (F40 q). Notation F56 := (F56 q).
  Notation F72 := (F72 q). Notation F76 := (F76 q). Notation F84 := (F84 q). Notation F88 := (F88 q).
  Ltac sgtcall T TY cur := sgtcall_ (q + -208)%Z lo S T TY MB A cur len cap bs.

  #[using="VOK"] Lemma dir_tab : forall (fp G cs cur : Z) gp tp (F : bvmap 5 word) fc
      x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x19 x28 x29 x30 x31 (w8 ty36 tb tl e72 ty84 tb2 tl2 : word) m,
    SCc m cur -> MBc m -> BUFc m -> (cur0 <= cur <= len)%Z ->
    F0 m w8 cs -> F36 m ty36 -> F40 m tb tl -> F56 m -> F72 m e72 -> F76 m -> F84 m ty84 -> F88 m tb2 tl2 ->
    stk rsegs m lo qq -> mem_inv rsegs m -> (0 <= fp /\ fp + 2 < 2^63)%Z -> (q + 16 <= G <= q + 64)%Z -> (0 <= cs <= 1)%Z ->
    evt rsegs (dpost gp tp F fc (fp + 1) G cs W0 (fun m' r cur' => r = PARSE_OK -> cur + 1 <= cur')%Z (fun _ => False) m)
        (headst gp tp F fc fp 9 G x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x19 x28 x29 x30 x31 m).
  Proof.
    vok VOK.
    intros until m. intros SC MBC BUF CUR FR0 FR36 FR40 FR56 FR72 FR76 FR84 FR88 ST MI FP GR CS.
    unfold headst. unfold SCc in SC. unfold MBc, mbuf_cells, MEMBUF_DEF_SIZE_INC in MBC. unfold BUFc in BUF.
    unfold F0 in FR0. unfold F36 in FR36. unfold F40 in FR40. unfold F56 in FR56. unfold F72 in FR72. unfold F76 in FR76. unfold F84 in FR84. unfold F88 in FR88. dex.
    pose proof (munch_refl W0 m) as MU. pose proof (wmono_refl rsegs m) as WM.
    pose proof (bytes_at_bound _ _ _ _ BUF) as BB.
    zstep. lit_branch.
    zstep. zstep. zstep. zstep.
    sgtcall (q + -168) (q + -172) cur.
    lazymatch goal with |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?r) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) => rename r into rr end.
    unfold PARSE_OK, PARSE_INCOMPLETE, PARSE_FAILURE in RES.
    destruct RES as [(tlz & ty & HR & -> & -> & -> & TL1 & -> & _ & TY5 & STRICT & CRB & CRL)|(HR & -> & ->)].
    -   zstep. rewrite (sx32_lit ty) by lia. zstep. zstep. zstep. zstep. zstep. zstep. if_cases K1; zify_cond K1.
      + cond_norm K1. all: zstep; zstep; dfinish rr (cur + tlz)%Z.
      + zstep. zstep. zstep. dfinish 5 (cur + tlz)%Z.
    - pose proof (word_lt64 ty36) as TYB.
      zstep. zstep. zstep. zstep. zstep. zstep. zstep. if_cases K1; zify_cond K1.
      + zstep. zstep. dfinish rr cur.
      + zstep. zstep. zstep. dfinish 5 cur.
  Qed.

  #[using="VOK"] Lemma sp_loop : forall (k : nat) (fp G cs cur curi : Z) gp tp (F : bvmap 5 word) fc (w8 : word) m0
      x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x28 x29 x30 x31 m,
    (len - curi < Z.of_nat k)%Z -> (cur0 <= cur <= curi)%Z -> (curi <= len)%Z ->
    linv W0 m0 m curi w8 cs -> (0 <= fp /\ fp + 2 < 2^63)%Z -> (q + 16 <= G <= q + 64)%Z -> (0 <= cs <= 1)%Z ->
    evt rsegs (dpost gp tp F fc (fp + 1) G cs W0 (fun m' r cur' => r = PARSE_OK -> cur <= cur')%Z (fun _ => False) m0)
      (MS (mkR x1 (wz qq) gp tp x5 x6 x7 (wz S) (wz G) x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 (wz (fp + 1))
               (wz 37) (wz 1) (wz 4) (wz 9) (wz 32) (wz 2) (wz cur0) x28 x29 x30 x31)
          F (wz 0x1426c) fc None m (seg_rom rsegs)).
  Proof.
    vok VOK.
    induction k as [|k IH]; intros until m; intros HK HC HL LI FP GR CS; [lia|].
    open_linv LI.
    pose proof (bytes_at_bound _ _ _ _ BUF) as BB.
    pose proof (rw_cells_bound rsegs _ _ _ SC) as SB. cbn [cells_size csize Nat.add] in SB.
    zstep. zstep. zstep. zstep. zstep.
    sgtcall (q + -120) (q + -136) curi. name_r.
    unfold PARSE_OK, PARSE_INCOMPLETE, PARSE_FAILURE in RES.

    assert (TAIL : forall (r : Z) y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y18 y19 y28 y29 y30 y31 m',
      linv W0 m0 m' curi w8 cs -> (r = 1 \/ r = 3 \/ r = 4)%Z ->
      evt rsegs (dpost gp tp F fc (fp + 1) G cs W0 (fun m' r cur' => r = PARSE_OK -> cur <= cur')%Z (fun _ => False) m0)
        (MS (mkR y1 (wz qq) gp tp y5 y6 y7 (wz S) (wz G) (wz r) y11 y12 y13 y14 y15 y16 y17 y18 y19 (wz (fp + 1))
                 (wz 37) (wz 1) (wz 4) (wz 9) (wz 32) (wz 2) (wz cur0) y28 y29 y30 y31)
            F (wz 0x142b8) fc None m' (seg_rom rsegs))).
    { intros until m'. intros LI' HR. clear - LO0 LOQ QMB MBS SHI BLO ANZ LBS CUR0 CAP AHI HC HL FP GR CS LI' HR. open_linv LI'.
      pose proof (rw_cells_bound rsegs _ _ _ SC) as SB. cbn [cells_size csize Nat.add] in SB.
      zstep. if_cases K0; zify_cond K0.
      - zstep. dfinish r curi.
      - zstep. zstep. if_cases K1; zify_cond K1. { exfalso. first [ apply K1; reflexivity | lia ]. }
        zstep. zstep. zstep. dfinish 1 curi. }
    destruct RES as [(tlz & ty & HR & -> & -> & -> & TL1 & -> & _ & TY5 & STRICT & CRB & CRL)|(HR & -> & ->)].
    - zstep. if_cases K0; zify_cond K0. { exfalso; lia. }
      zstep. rewrite (sx32_lit ty) by lia. zstep. if_cases K1; zify_cond K1.
      +   zstep. zstep. if_cases K2; zify_cond K2. { exfalso. first [ apply K2; reflexivity | lia ]. }
        zstep. if_cases K3; zify_cond K3.
        *   eapply (IH fp G cs cur (curi + tlz)%Z); try lia. close_linv.
        *   sstep. apply (TAIL 4); [| lia]. close_linv.
      +   zstep. zstep. zstep. zstep.
        sgtcall (q + -120) (q + -136) (curi + tlz)%Z. name_r.
        unfold PARSE_OK, PARSE_INCOMPLETE, PARSE_FAILURE in RES.
        destruct RES as [(tlz2 & ty2 & HR2 & -> & -> & -> & TL2 & -> & _ & TY52 & STRICT2 & CRB2 & CRL2)|(HR2 & -> & ->)].
        * zstep. rewrite (sx32_lit ty2) by lia. zstep. if_cases K4; zify_cond K4. 2:{ exfalso; lia. }
          zstep. if_cases K3; zify_cond K3.
          -- eapply (IH fp G cs cur (curi + tlz + tlz2)%Z); try lia. close_linv.
          -- sstep. apply (TAIL rr); [| lia]. close_linv.
        * zstep. rewrite (sx32_lit ty) by lia. zstep. if_cases K4; zify_cond K4. { exfalso; lia. }
          zstep. sstep. apply (TAIL rr); [| lia]. close_linv.
    - zstep. if_cases K0; zify_cond K0. 2:{ exfalso; lia. }
      apply (TAIL rr); [| lia]. close_linv.
  Qed.

  #[using="VOK"] Lemma dir_sp : forall (fp G cs cur : Z) gp tp (F : bvmap 5 word) fc
      x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x19 x28 x29 x30 x31 (w8 ty36 tb tl e72 ty84 tb2 tl2 : word) m,
    SCc m cur -> MBc m -> BUFc m -> (cur0 <= cur <= len)%Z ->
    F0 m w8 cs -> F36 m ty36 -> F40 m tb tl -> F56 m -> F72 m e72 -> F76 m -> F84 m ty84 -> F88 m tb2 tl2 ->
    stk rsegs m lo qq -> mem_inv rsegs m -> (0 <= fp /\ fp + 2 < 2^63)%Z -> (q + 16 <= G <= q + 64)%Z -> (0 <= cs <= 1)%Z ->
    evt rsegs (dpost gp tp F fc (fp + 1) G cs W0 (fun m' r cur' => r = PARSE_OK -> cur <= cur')%Z (fun _ => False) m)
        (headst gp tp F fc fp 32 G x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x19 x28 x29 x30 x31 m).
  Proof.
    vok VOK.
    intros until m. intros SC MBC BUF CUR FR0 FR36 FR40 FR56 FR72 FR76 FR84 FR88 ST MI FP GR CS. unfold headst.
    pose proof (munch_refl W0 m) as MU. pose proof (wmono_refl rsegs m) as WM.
    zstep. lit_branch. zstep. lit_branch.
    eapply (sp_loop (Datatypes.S (Z.to_nat (len - cur))) fp G cs cur cur); try lia.
    unfold F0, F36, F40, F56, F72, F76, F84, F88 in *. close_linv.
  Qed.
End VFW.
