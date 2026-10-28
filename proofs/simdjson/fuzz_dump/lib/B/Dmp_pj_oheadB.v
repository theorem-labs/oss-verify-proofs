From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep StoreFast FP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.P Require Import Str_tac Sj_stage1_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Sj Require Import SjTape SjTapeList SjTapeTile.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import Layout RT_iface RT_iface2 D_defs D_kit D_clx D_rlkit D_libiface I_lkit Sj_akit Sj_acps Sj_hkit Atp_fzwA Atp_defsA Atp_objwA Atp_objnA Pj_defsA El_defsA Dmp_hdefsA Dmp_pj_ifaceA Dmp_pj_kitA Dmp_pj_leafA Dmp_pj_strA Dmp_pj_arrA Dmp_pj_objA El_os_defsA Pj_ser_trefA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Ltac oh_hook := match goal with H : _ / 72057594037927936 = _ |- _ => progress rewrite H end.
Ltac oh_gt := let G := fresh "G" in if_cases G; zify_cond G; [exfalso; rewrite ?unsigned_lit in G by lia; rewrite ?land7_mod in G by lia; lia|]; try clear G.
Ltac oh_gt2 := let G := fresh "G" in if_cases G; zify_cond G; [|exfalso; rewrite ?unsigned_lit in G by lia; rewrite ?land7_mod in G by lia; lia]; try clear G.
Ltac oh_step := first [ ls | if_false | if_true | (progress rewrite ?shr3_div) | (shz_norm; ls) | oh_gt | oh_gt2
                      | (progress rewrite ?Z.shiftr_div_pow2 by lia) | oh_hook ].
Ltac oh_notat := tryif pr_at [0xafc0c; 0xaf59c; 0xaf738] then fail else idtac.
Tactic Notation "oh_walk" int_or_var(n) := do n (try (oh_notat; oh_step)).

Ltac oh_tix ret :=
  lazymatch goal with
  | OK : aenvA_ok ?E, AI : AINV_A ?E ?m, CC : client_consts ?m, MU : munch ?W ?m ?mx |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
    pose proof (AINV_A_munch _ _ _ _ OK AI MU ltac:(repeat constructor; cbn [fst]; lia)) as AIx;
    pose proof (client_consts_munch _ _ _ CC MU ltac:(intros x Hx; cbn [outside]; lia)) as CCx;
    eapply evt_cut; [eapply pj_tixE; [exact OK | exact AIx | exact CCx | eassumption | lia | lia | lia | lia | eassumption] |];
    clear AIx CCx; cbv beta;
    let m2 := fresh "m" in let a4' := fresh "a" in let MU2 := fresh "MUt" in let WM2 := fresh "WMt" in let MI2 := fresh "MI" in
    let ST2 := fresh "ST" in let AI2 := fresh "AIt" in let CC2 := fresh "CC" in
    intros ? (m2 & a4' & -> & MU2 & WM2 & MI2 & ST2 & AI2 & CC2);
    rewrite (ret_pc_even ret) by lia;
    lazymatch goal with WM : wmono _ m mx |- _ =>
      let MU3 := fresh "MU" in let WM3 := fresh "WM" in
      let W2 := lazymatch type of MU2 with munch ?w _ _ => w end in
      pose proof (munch_trans _ _ _ _ MU (munch_weaken W2 W _ _ ltac:(intros x Hx; cbn [outside] in *; lia) MU2)) as MU3;
      pose proof (wmono_trans _ _ _ _ WM WM2) as WM3;
      repeat match goal with FR : rw_cells _ mx _ _ |- _ =>
        let FR2 := fresh "FR" in pose proof (rw_cells_transport _ _ _ _ _ _ FR MU2 WM2) as FR2;
        specialize (FR2 ltac:(cbn [disjoint_from cells_size csize Nat.add map]; repeat split; lia)); clear FR end;
      clear MU WM MU2 WM2
    end
  end.

Lemma pj_tape_read_lo4 : forall m TAPE (tws : list Z) (i : Z),
  bytes_at bsegs m TAPE (u64s (map (Z_to_bv 64) tws)) -> 0 <= i < Z.of_nat (length tws) ->
  ov_read_bytes bsegs m (wa (TAPE + 8 * i)) 4 = Some (le4 (Z_to_bv 64 (Tf tws i))).
Proof.
  intros m TAPE tws i HB Hi.
  rewrite (bytes_at_read bsegs m TAPE _ (8 * i) 4 HB); [| lia| rewrite u64s_length, length_map; lia].
  replace (Z.to_nat (8 * i)) with (8 * Z.to_nat i)%nat by lia.
  replace (firstn 4 (skipn (8 * Z.to_nat i) (u64s (map (Z_to_bv 64) tws))))
    with (firstn 4 (firstn 8 (skipn (8 * Z.to_nat i) (u64s (map (Z_to_bv 64) tws))))) by (rewrite firstn_firstn; reflexivity).
  rewrite u64s_read by (rewrite length_map; lia). f_equal.
  unfold Tf. rewrite (map_nth (Z_to_bv 64)). unfold le8, le4, word_to_le_bytes. reflexivity.
Qed.

Lemma pj_ohead2 : forall (E : aenvA) (q f osp i e cv : Z) (j0 j8 j16 j24 j32 j40 j48 j56 j64 j72 j96 jC : list byte)
    (gp ra a1 a2 a3 a4 a5 a6 a7 s6 s8 s9 s11 t0 t1 t2 t3 t4 t5 t6 : word) F fc (m : mem),
  aenvA_ok E -> 0 <= i -> i < e -> e + 1 <= ae_n E -> ae_n E < 2^32 -> 0 <= cv <= CNT_MAX -> ae_T E i = cword t_obj (e + 1) cv ->
  0x6d5000 <= q - 256 -> ae_lo E <= q - 272 -> q < 2^63 -> 0 < osp < 2^63 -> osp mod 8 = 0 -> 0 < f -> f + 256 < 2^63 -> shad f + 32 < 2^63 ->
  AINV_A E m -> client_consts m -> stk bsegs m (ae_lo E) (q - 256) -> shz m (ae_TAPE E) (8 * ae_n E) ->
  rw_cells bsegs m (q - 256) [CB 8 j0; CB 8 j8; CB 8 j16; CB 8 j24; CB 8 j32; CB 8 j40; CB 8 j48; CB 8 j56; CB 8 j64; CB 8 j72;
                              C8 (Z_to_bv 64 SHB); C8 (Z_to_bv 64 osp); CB 8 j96; C8 (Z_to_bv 64 f); CB 24 jC; C8 (Z_to_bv 64 (ae_DOC E)); C8 (Z_to_bv 64 i)] ->
  mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m' : mem) (rax a0x a1x a2x a3x a4x s2x s10x : word),
      munch [(q - 272, q - 256); (q - 256, q - 256 + 80)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' (ae_lo E) (q - 256) /\
      ((i + 1 = e /\
         ms = MS (mkR rax (Z_to_bv 64 (q - 256)) gp (Z_to_bv 64 TPV_A) t0 t1 t2 (Z_to_bv 64 q) (Z_to_bv 64 (q - 256)) a0x (Z_to_bv 64 DMP_LIT_RBRC_A)
                      a2x a3x a4x a5 a6 a7 s2x (Z_to_bv 64 f) (Z_to_bv 64 i) (Z_to_bv 64 (ae_DOC E)) (Z_to_bv 64 (i + 1)) (Z_to_bv 64 f) s8
                      (Z_to_bv 64 SHB) s10x (Z_to_bv 64 (shad f)) t3 t4 t5 t6) F (Z_to_bv 64 DMP_PJ_CLOSE_A) fc None m' (seg_rom bsegs)
         /\ rw_cells bsegs m' (q - 256) [CB 8 j0; CB 8 j8; CB 8 j16; CB 8 j24; CB 8 j32; CB 8 j40; CB 8 j48; CB 8 j56; C8 (Z_to_bv 64 e);
                                         C8 (Z_to_bv 64 (ae_DOC E)); C8 (Z_to_bv 64 SHB); C8 (Z_to_bv 64 osp); CB 8 j96; C8 (Z_to_bv 64 f); CB 24 jC;
                                         C8 (Z_to_bv 64 (ae_DOC E)); C8 (Z_to_bv 64 i)])
      \/ (i + 1 <> e /\
         ms = MS (pjRO E q f (i + 1) gp rax a0x a1x a2x a3x a4x a5 a6 a7 (Z_to_bv 64 i) (Z_to_bv 64 ((ae_DOC E + 8) / 8)) s10x t0 t1 t2 t3 t4 t5 t6)
                 F (Z_to_bv 64 DMP_PJ_OLOOP_A) fc None m' (seg_rom bsegs)
         /\ rw_cells bsegs m' (q - 256) (pj_oframe E f e osp ++ [CB 8 j96; C8 (Z_to_bv 64 f); CB 24 jC; C8 (Z_to_bv 64 (ae_DOC E)); C8 (Z_to_bv 64 i)]))))
    (MS (pjR q f gp ra (Z_to_bv 64 osp) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (ae_DOC E)) (Z_to_bv 64 i) s6 s8 s9 s11 t0 t1 t2 t3 t4 t5 t6)
        F (Z_to_bv 64 DMP_PJ_OHEAD_A) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros OK I0 IE EN N32 CV TW QLO LOQ QH OR O8 F0 FH SFH AI CC ST SHZ0 FR MI.
  pose proof OK as OK'. destruct OK' as [WF SBS P1 P1L (T16 & NT8 & TN & TS & TL) _ _ _ (D8 & DF & DL & DS & DT) LOW [HL HT]].
  unfold USTACK_TOP in HT. unfold SEGTOP_A in *.
  assert (SHZT : forall m', munch [(q - 272, q - 256); (q - 256, q - 256 + 80)] m m' -> wmono bsegs m m' -> shz m' (ae_TAPE E) (8 * ae_n E)).
  { intros m' MU' _. eapply shz_munch_hi; [exact SHZ0| exact MU'| lia| lia|].
    intros y Hy. cbn [outside]. repeat (split; try exact I); lia. }
  assert (FS0 : 0 <= fs_size (ae_kD E)) by (unfold fs_size; apply Z.shiftl_nonneg; lia).
  assert (ED : bv_unsigned (Z_to_bv 64 (ae_DOC E)) = ae_DOC E) by (apply unsigned_lit; lia).
  assert (EI : bv_unsigned (Z_to_bv 64 i) = i) by (apply unsigned_lit; lia).
  assert (ESP : bv_unsigned (Z_to_bv 64 (q - 256)) = q - 256) by (apply unsigned_lit; lia).
  assert (EF : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).
  assert (EO : bv_unsigned (Z_to_bv 64 osp) = osp) by (apply unsigned_lit; lia).
  unfold CNT_MAX in CV.
  assert (TIR : 0 <= ae_T E i < 2^64) by (rewrite TW; unfold cword, tword, t_obj; lia).
  unfold pjR, shad, SHB, DMP_PJ_OHEAD_A, DMP_PJ_CLOSE_A, DMP_PJ_OLOOP_A, DMP_LIT_RBRC_A in *.
  pose proof (munch_refl [(q - 272, q - 256); (q - 256, q - 256 + 80)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  oh_walk 40.
  oh_tix 0xaefcc.
  match goal with MU : munch _ m ?mx, WM : wmono _ m ?mx |- _ => pose proof (SHZT _ MU WM) as SHZ1 end.
  pose proof AIt as (TAPEB1 & _ & _ & DOCC1 & DSH1).
  chk0 SHZ1 (ae_TAPE E + 8 * i).
  assert (TYO : ttype (ae_T E i) = 123).
  { rewrite TW. unfold ttype, cword, tword, t_obj. rewrite Z.div_add_l by lia. rewrite Z.div_small by lia. lia. }
  pose proof (tape_read_typeA _ _ _ i TAPEB1 ltac:(lia) ltac:(lia)) as RT7. rewrite TYO in RT7.
  oh_walk 40.
  oh_tix 0xaf3d0.
  clear SHZ1 RT7. try clear TAPEB1; try clear DOCC1; try clear DSH1.
  match goal with MU : munch _ m ?mx, WM : wmono _ m ?mx |- _ => pose proof (SHZT _ MU WM) as SHZ1 end.
  pose proof AIt0 as (TAPEB1 & _ & _ & DOCC1 & DSH1).
  chk0 SHZ1 (ae_TAPE E + 8 * i).
  pose proof (tape_read_typeA _ _ _ i TAPEB1 ltac:(lia) ltac:(lia)) as RT7. rewrite TYO in RT7.
  oh_walk 60.
  oh_tix 0xaf574.
  clear SHZ1 RT7. try clear TAPEB1; try clear DOCC1; try clear DSH1.
  match goal with MU : munch _ m ?mx, WM : wmono _ m ?mx |- _ => pose proof (SHZT _ MU WM) as SHZ1 end.
  pose proof AIt1 as (TAPEB1 & _ & _ & DOCC1 & DSH1).
  chk0 SHZ1 (ae_TAPE E + 8 * i).
  pose proof (pj_tape_read_lo4 _ _ _ i TAPEB1 ltac:(lia)) as RL4.
  assert (ZX : bv_unsigned (zx32 (Z_to_bv 64 (ae_T E i))) = e + 1).
  { rewrite TW. unfold zx32, cword, tword, t_obj. rewrite (unsigned_lit (_ mod 2^32)) by (Z.div_mod_to_equations; lia).
    rewrite unsigned_lit by lia. Z.div_mod_to_equations; lia. }
  oh_walk 60.
  rewrite ?ZX.
  rewrite ?ZX.
  let G := fresh "G" in if_cases G; zify_cond G.
  - oh_walk 80.
    apply evt_done. do 9 eexists. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
    right. split; [lia|]. split.
    + unfold pjRO, shad, SHB. rewrite ?shr3_div. atp_st_eq_goal.
    + unfold pj_oframe, DMP_LIT_RBRC_A, DMP_LIT_QCOL_A, DMP_LIT_QUOT_A, SHB. cbn [app].
      match goal with H : rw_cells bsegs ?mm (q - 256) _ |- rw_cells bsegs ?mm (q - 256) _ =>
        rewrite ?ZX in H; replace (e + 1 + -1) with e in H by lia; exact H end.
  - oh_walk 60.
    apply evt_done. do 9 eexists. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
    left. split; [lia|]. split.
    + atp_st_eq_goal.
    + match goal with H : rw_cells bsegs ?mm (q - 256) _ |- rw_cells bsegs ?mm (q - 256) _ =>
        rewrite ?ZX in H; replace (e + 1 + -1) with e in H by lia; exact H end.
Unshelve. all: exact (Z_to_bv 64 0).
Qed.
