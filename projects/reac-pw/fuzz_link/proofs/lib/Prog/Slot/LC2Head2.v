(* Arm c2 (op_mark), piece HEAD, second segment: the call of kernel at 0x13d48 (c2h_13d48) -> c2_13d70.
   0x13d48 - 0x13d4c: a0 = &in (sp + 0x40), jal kernel (kernel_c.v's leaf contract, the only Section
   hypothesis); 0x13d50 - 0x13d6c: model_begin (fuzz_link.c:668-675): md->socket_errno, md->send_errno :=
   the fake kernel's, md->next := 0, md->n_req := 0, g_nl.n_sent := 0. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem kernel_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import Tac.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog.Slot Require Import
  LDefs LC2Defs LC2HeadA LC2HeadB LC2HeadC LC2Head1.
Local Open Scope Z_scope.

(* ==========================================================================
   1. A leaf call inside a segment stated up to ms_eqv, continued on the canonical mkR state
   ========================================================================== *)

Lemma c2h_eqv_cl_eqv : forall (Q : machine_state -> Prop) c a, eqv_cl Q c -> Regs6ss.ms_eqv c a -> eqv_cl Q a.
Proof. intros Q c a (c0 & H & E0) E. exists c0. split; [exact H | exact (c2_ms_eqv_trans _ _ _ E0 E)]. Qed.

Lemma c2h_leaf_run : forall pc K Pre Wr Post (Q : machine_state -> Prop),
  leaf pc K Pre Wr Post ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z),
  Pre (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) m ->
  mem_inv rsegs m -> stk rsegs m lo (bv_unsigned sp) -> lo + K <= bv_unsigned sp -> bv_unsigned sp < 2 ^ 63 ->
  (forall (regs' : bvmap 5 word) (m' : word -> option byte),
     munch ((bv_unsigned sp - K, bv_unsigned sp)
              :: Wr (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) m)
           m m' ->
     wmono rsegs m m' -> mem_inv rsegs m' -> stk rsegs m' lo (bv_unsigned sp) ->
     Post (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) m regs' m' ->
     evt rsegs (eqv_cl Q)
       (MS (mkR (reg_get regs' 1) sp gp tp (reg_get regs' 5) (reg_get regs' 6) (reg_get regs' 7) s0 s1
                (reg_get regs' 10) (reg_get regs' 11) (reg_get regs' 12) (reg_get regs' 13) (reg_get regs' 14)
                (reg_get regs' 15) (reg_get regs' 16) (reg_get regs' 17)
                s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                (reg_get regs' 28) (reg_get regs' 29) (reg_get regs' 30) (reg_get regs' 31))
           F (ret_pc ra) fc None m' (seg_rom rsegs))) ->
  evt rsegs (eqv_cl Q)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).
Proof.
  intros pc K Pre Wr Post Q HL ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
    t3 t4 t5 t6 F fc m lo HP MI ST LO SP K'.
  specialize (HL _ F fc m lo HP MI ST LO SP).
  eapply evt_cut; [exact HL|].
  intros ms' (regs' & m' & -> & RP & MU & WM & MI' & ST' & PO).
  change (spZ (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6))
    with (bv_unsigned sp) in MU, ST'.
  change (getr (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) 1)
    with ra.
  assert (R2 : reg_get regs' 2 = sp) by exact (RP 2 ltac:(cbv [callee_saved]; lia)).
  assert (R3 : reg_get regs' 3 = gp) by exact (RP 3 ltac:(cbv [callee_saved]; lia)).
  assert (R4 : reg_get regs' 4 = tp) by exact (RP 4 ltac:(cbv [callee_saved]; lia)).
  assert (R8 : reg_get regs' 8 = s0) by exact (RP 8 ltac:(cbv [callee_saved]; lia)).
  assert (R9 : reg_get regs' 9 = s1) by exact (RP 9 ltac:(cbv [callee_saved]; lia)).
  assert (R18 : reg_get regs' 18 = s2) by exact (RP 18 ltac:(cbv [callee_saved]; lia)).
  assert (R19 : reg_get regs' 19 = s3) by exact (RP 19 ltac:(cbv [callee_saved]; lia)).
  assert (R20 : reg_get regs' 20 = s4) by exact (RP 20 ltac:(cbv [callee_saved]; lia)).
  assert (R21 : reg_get regs' 21 = s5) by exact (RP 21 ltac:(cbv [callee_saved]; lia)).
  assert (R22 : reg_get regs' 22 = s6) by exact (RP 22 ltac:(cbv [callee_saved]; lia)).
  assert (R23 : reg_get regs' 23 = s7) by exact (RP 23 ltac:(cbv [callee_saved]; lia)).
  assert (R24 : reg_get regs' 24 = s8) by exact (RP 24 ltac:(cbv [callee_saved]; lia)).
  assert (R25 : reg_get regs' 25 = s9) by exact (RP 25 ltac:(cbv [callee_saved]; lia)).
  assert (R26 : reg_get regs' 26 = s10) by exact (RP 26 ltac:(cbv [callee_saved]; lia)).
  assert (R27 : reg_get regs' 27 = s11) by exact (RP 27 ltac:(cbv [callee_saved]; lia)).
  pose proof (RegisterBridge.canonical_contract_transport rsegs (eqv_cl Q)
                (MS regs' F (ret_pc ra) fc None m' (seg_rom rsegs))) as T.
  eapply evt_mono; [apply T|].
  2:{ intros a (c & HQ & E). exact (c2h_eqv_cl_eqv _ _ _ HQ E). }
  change (evt rsegs (eqv_cl Q) (MS (Regs6ss.mkR_of regs') F (ret_pc ra) fc None m' (seg_rom rsegs))).
  unfold Regs6ss.mkR_of.
  rewrite R2, R3, R4, R8, R9, R18, R19, R20, R21, R22, R23, R24, R25, R26, R27.
  exact (K' regs' m' MU WM MI' ST' PO).
Qed.

(* ==========================================================================
   2. kernel_contract's Pre at the call (0x13d4c, a0 = sp + 0x40)
   ========================================================================== *)

Lemma c2h_kpre : forall (regs : bvmap 5 word) (m : word -> option byte) (S md mk p0 : Z) (pl sv : list byte)
    (gbs kbs : list byte) (P N : Z),
  lenv_ok (LEnv S md mk p0 pl sv) -> c2h_kregs regs -> arg regs 0 = S - 480 + 64 ->
  rw_cells rsegs m (S - 480 + 64) [C8 (Z_to_bv 64 P); C8 (Z_to_bv 64 N)] ->
  c2h_keep (LEnv S md mk p0 pl sv) gbs m -> c2h_cur (LEnv S md mk p0 pl sv) P N ->
  nlk_at m kbs -> nlk_wf kbs -> iftab_at m kbs link_tab -> la_ok m -> mem_inv rsegs m ->
  exists kb (wp wn : word),
       nlk_at m kb /\ frame_apart_gnl regs 4416 /\ nlk_wf kb
       /\ rw_cells rsegs m (arg regs 0) [C8 wp; C8 wn]
       /\ apart_gnl (arg regs 0) 16 /\ apart_frame regs 4416 (arg regs 0) 16
       /\ (exists d, bytes_at rsegs m (bv_unsigned wp) d /\ Z.of_nat (length d) = bv_unsigned wn)
       /\ kernel_apart regs (bv_unsigned wp) (bv_unsigned wn)
       /\ kernel_apart regs A_TEXTS (8 * TEXTS_N)
       /\ (forall i, 0 <= i < TEXTS_N -> exists p s slack,
             u64_at m (A_TEXTS + 8 * i) p /\ p <> 0
             /\ bytes_at rsegs m p (s ++ zb 0 :: slack) /\ ~ In (zb 0) s
             /\ (- (p + Z.of_nat (length s) + 1)) mod 8 <= Z.of_nat (length slack)
             /\ Z.of_nat (length s) < NL_CHUNK_MAX
             /\ kernel_apart regs p (Z.of_nat (length s) + 1 + Z.of_nat (length slack)))
       /\ (exists la sl,
             rw_cells rsegs m A_LONG_ALIAS [CB (Z.to_nat 300) la; C1 (zb 0)]
             /\ bytes_at rsegs m (A_LONG_ALIAS + LONG_ALIAS_SIZE) sl /\ length sl = 3%nat)
       /\ apart_frame regs 4416 A_LONG_ALIAS (LONG_ALIAS_SIZE + 3)
       /\ (arg regs 0 + 16 <= A_LONG_ALIAS \/ A_LONG_ALIAS + LONG_ALIAS_SIZE + 3 <= arg regs 0)
       /\ (forall tab i nm ix p, iftab_at m kb tab -> nth_error tab i = Some (nm, ix) ->
             u64_at m (A_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p ->
             kernel_apart regs p (Z.of_nat (length nm) + 1)).
Proof.
  intros regs m S md mk p0 pl sv gbs kbs P N HE KR A0 HCC K HCUR HNK HW HIF HLA MI.
  pose proof KR as (KR1 & KR2 & KR3).
  pose proof HE as HE'. unfold lenv_ok in HE'. cbn [e_S e_md e_mk e_p0 e_pl e_saved] in HE'.
  destruct HE' as (HS1 & HS2 & HS3 & BMD & BMK & Hmd16 & Hmk16 & Hmdmk & Hpl1 & BPL & Hplmd & Hplmk & Hsv).
  destruct (c2h_blk_where S p0 (Z.of_nat (length pl)) ltac:(lia) BPL) as (Hp01 & Hp02 & Hplw).
  clear BMD BMK Hmdmk Hplmd Hplmk.
  destruct HCUR as (k & Hk & EP & EN). cbn [e_p0 e_pl] in Hk, EP, EN.
  pose proof K as (_ & _ & _ & _ & K5 & K6 & _ & _ & _ & K10 & _).
  cbn [e_p0 e_pl] in K10.
  unfold SLOT_STACK_Z in Hp02.
  assert (SP : spZ regs = S - 480) by lia.
  assert (UP : bv_unsigned (Z_to_bv 64 P) = P) by (apply unsigned_lit; lia).
  assert (UN : bv_unsigned (Z_to_bv 64 N) = N) by (apply unsigned_lit; lia).
  exists kbs, (Z_to_bv 64 P), (Z_to_bv 64 N).
  rewrite UP, UN, A0.
  split; [exact HNK|].
  split; [unfold frame_apart_gnl, apart_gnl; unfold A_G_NL, NK_SIZE; lia|].
  split; [exact HW|].
  split; [exact HCC|].
  split; [unfold apart_gnl, A_G_NL, NK_SIZE; lia|].
  split; [unfold apart_frame; lia|].
  split.
  { exists (skipn (Z.to_nat k) pl). split.
    - pose proof (c2h_bytes_at_skipn _ _ _ (Z.to_nat k) K10 ltac:(lia)) as B.
      rewrite Z2Nat.id in B by lia. rewrite EP. exact B.
    - rewrite length_skipn. lia. }
  split.
  { apply c2h_kapart_heap; [exact KR | lia | lia | unfold SLOT_STACK_Z; lia | lia]. }
  split; [apply c2h_kapart_lo; [exact KR | unfold TEXTS_N; lia | unfold A_TEXTS, TEXTS_N, A_G_NL; lia]|].
  split; [exact (c2h_texts_pre regs m KR K5 MI)|].
  split; [exact HLA|].
  split; [unfold apart_frame, A_LONG_ALIAS, LONG_ALIAS_SIZE; lia|].
  split; [unfold A_LONG_ALIAS, LONG_ALIAS_SIZE; lia|].
  exact (c2h_iface_pre regs m kbs KR HIF K6).
Qed.

(* ==========================================================================
   3. The end of the segment
   ========================================================================== *)

(* what the segment may write: kernel's frame, its part of g_nl, long_alias, the cursor cells, and the
   five stores of model_begin *)
Definition c2h_W (S md : Z) : list ivl :=
  [(S - 480 - 4416, S - 480); (A_G_NL + NK_CHUNK, A_G_NL + NK_OPEN);
   (A_LONG_ALIAS, A_LONG_ALIAS + LONG_ALIAS_SIZE); (S - 480 + 64, S - 480 + 64 + 16);
   (md, md + 12); (md + 8336, md + 8340); (474664, 474668)].

Definition c2h_Ws (md : Z) : list ivl := [(md, md + 12); (md + 8336, md + 8340); (474664, 474668)].

Ltac c2h_dj2 :=
  cbn [disjoint_from e_S e_md e_mk e_p0 e_pl e_saved];
  unfold c2h_W, c2h_Ws, c2h_img_lo, c2h_if_lo, c2h_if_n, A_G_NL, NK_IF_NAME, NK_N_IF, NK_SIZE, NK_OPEN,
    NK_CHUNK, NK_N_SENT, A_G_NAMES, A_GUARD_S, MK_SIZE, MD_SIZE, A_LONG_ALIAS, LONG_ALIAS_SIZE, SLOT_STACK_Z,
    SLOT_FRAME, MD_N_REQ in *;
  cbn [disjoint_from]; lia.

Lemma c2h_h2_fin : forall (S md mk p0 : Z) (pl sv : list byte) (i : Z) (gp : word) (s : Z)
    (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m0 m2 m7 : word -> option byte) (P N k adv : Z)
    (j0 j1 j2 kbs mbs gbs kbs2 la2 kb3 mb3 : list byte) (v0 v1 : word),
  lenv_ok (LEnv S md mk p0 pl sv) ->
  c2h_keep (LEnv S md mk p0 pl sv) gbs m0 -> MemNorm.task_mem rsegs m0 ->
  c2h_kfacts i kbs -> model_wf mbs -> marks_wf gbs -> marks_are gbs mbs -> Z.of_nat (length mbs) = MD_SIZE ->
  nlk_wf kbs2 -> Z.of_nat (length kbs2) = NK_SIZE -> nk_next kbs2 = 0 -> nk_open kbs2 = nk_open kbs ->
  nk_opened kbs2 = nk_opened kbs -> nk_closed kbs2 = nk_closed kbs -> nk_misuse kbs2 = nk_misuse kbs ->
  iftab_at m2 kbs2 link_tab -> ifptrs_at m2 -> munch (c2h_Ws md) m2 m7 ->
  munch (c2h_W S md) m0 m7 -> wmono rsegs m0 m7 ->
  u8arr rsegs m7 A_G_NL kb3 -> kb3 = c2h_kbs kbs2 ->
  u8arr rsegs m7 md mb3 -> mb3 = c2h_mbs mbs v0 v1 ->
  v0 = sx32 (Z_to_bv 64 (nk_socket_errno kbs2)) -> v1 = sx32 (Z_to_bv 64 (nk_send_errno kbs2)) ->
  rw_cells rsegs m7 A_LONG_ALIAS [CB (Z.to_nat 300) la2; C1 (zb 0)] ->
  rw_cells rsegs m7 (S - 480) (c2h_fhead md mk j0) ->
  rw_cells rsegs m7 (S - 480 + 64) [C8 (Z_to_bv 64 (P + adv)); C8 (Z_to_bv 64 (N - adv))] ->
  rw_cells rsegs m7 (S - 480 + 80) [CB 40 j1; CB 256 j2] ->
  mem_inv rsegs m7 -> stk rsegs m7 (S - 65536) (S - 480) ->
  0 <= k <= Z.of_nat (length pl) -> P = p0 + k -> N = Z.of_nat (length pl) - k -> 0 <= adv <= N ->
  frm0 fc -> 0 <= i <= 47 -> 0 <= s <= 255 ->
  c2_post (LEnv S md mk p0 pl sv) m0 (fun c => exists s, c2_13d70 (LEnv S md mk p0 pl sv) i gp s c)
    (MS (mkR ra (wz (S - SLOT_FRAME)) gp (wz A_TP) t0 t1 t2 (wz md) (wz GNL40) a0 a1 a2 a3 a4 a5 a6 a7
             (wz (sel_ptr s)) s3 s4 (wz 46) (wz A_JT) (wz mk) (wz 0xab) (wz 4) (wz (md + MD_N_REQ)) (wz i)
             t3 t4 t5 t6)
        F (wz 0x13d70) fc None m7 (seg_rom rsegs)).
Proof.
  intros S md mk p0 pl sv i gp s ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 t3 t4 t5 t6 F fc m0 m2 m7 P N k adv
    j0 j1 j2 kbs mbs gbs kbs2 la2 kb3 mb3 v0 v1
    HE K0 TM KF HMDwf HMKwf HMA HMDl HW2 HL2 HN2 HO2 HOD2 HCL2 HMI2 HIF2 HIFP2 MU2 MUA WMA HK3 EK3 HM3 EM3
    EV0 EV1 HLA FH FC FT MI ST Hk EP EN Hadv FRM Hi Hs.
  pose proof HE as HE'. unfold lenv_ok in HE'. cbn [e_S e_md e_mk e_p0 e_pl e_saved] in HE'.
  destruct HE' as (HS1 & HS2 & HS3 & BMD & BMK & Hmd16 & Hmk16 & Hmdmk & Hpl1 & BPL & Hplmd & Hplmk & Hsv).
  destruct (c2h_blk_where S md MD_SIZE ltac:(unfold MD_SIZE; lia) BMD) as (Hmd1 & Hmd2 & Hmdw).
  destruct (c2h_blk_where S mk MK_SIZE ltac:(unfold MK_SIZE; lia) BMK) as (Hmk1 & Hmk2 & Hmkw).
  destruct (c2h_blk_where S p0 (Z.of_nat (length pl)) ltac:(lia) BPL) as (Hp01 & Hp02 & Hplw).
  clear BMD BMK BPL.
  subst kb3 mb3.
  destruct (c2h_kbs_facts kbs2 HL2 HW2) as (KL & KW & KNS & KNX & KO & KOD & KCL & KMI & KIF & KSO & KSE).
  pose proof HW2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Rse & Rde & _).
  assert (E0 : bv_unsigned v0 mod 2 ^ 32 = nk_socket_errno kbs2)
    by (rewrite EV0, c2h_sx32_low; apply Z.mod_small; lia).
  assert (E1 : bv_unsigned v1 mod 2 ^ 32 = nk_send_errno kbs2)
    by (rewrite EV1, c2h_sx32_low; apply Z.mod_small; lia).
  destruct (c2h_mbs_facts mbs gbs v0 v1 _ _ HMDl HMDwf HMA Rse Rde E0 E1) as (ML & MW & MA & MSO & MSE & MNX & MNR).
  assert (K7 : c2h_keep (LEnv S md mk p0 pl sv) gbs m7)
    by (eapply c2h_keep_munch; [exact Hsv | exact K0 | exact MUA | exact WMA | c2h_dj2 ..]).
  destruct KF as (KW0 & KO0 & KM0 & KOC0 & KOP0).
  apply c2h_post_intro.
  - exists s. unfold c2_13d70. do 18 eexists.
    exists F, fc, m7, (P + adv), (N - adv), j0, j1, j2, (c2h_kbs kbs2), (c2h_mbs mbs v0 v1), gbs.
    split; [reflexivity|].
    split; [exact FRM|]. split; [exact Hi|]. split; [exact Hs|].
    split; [unfold c2_frame; cbn [e_S e_md e_mk]; apply c2h_frame_join; [exact FH | exact FC | exact FT]|].
    pose proof K7 as (K1 & K2 & K3 & K4 & K5 & K6 & K7' & K8 & K9 & K10 & sl & K11 & K12).
    split.
    { split; [exact K1|]. split; [exact K2|]. split; [exact K3|]. split; [exact K4|].
      split; [exists la2, sl; split; [exact HLA | split; [exact K11 | exact K12]]|].
      split; [exact K5|]. split; [exact K6|]. split; [exact K8|]. split; [exact K7'|].
      split; [exact MI|]. split; [|exact ST].
      eapply c2h_task_mem_munch; [exact TM | exact MUA |].
      intros x Hx HO. destruct (c2h_not_outside _ _ HO) as (lo & hi & Hin & Hr).
      unfold c2h_W in Hin. cbn [In] in Hin.
      repeat destruct Hin as [Ein|Hin]; try contradiction; injection Ein as <- <-;
        unfold A_G_NL, NK_OPEN, NK_CHUNK, A_LONG_ALIAS, LONG_ALIAS_SIZE, SLOT_STACK_Z, MD_SIZE in *; lia. }
    split.
    { split; [exact K10|]. exists (k + adv). cbn [e_pl e_p0]. lia. }
    split; [apply c2h_name_ok; [exact K2 | exact K3 | exact MI | exact Hs]|].
    split.
    { split; [split; [exact HK3 | exact KL]|].
      split; [exact KW|].
      split.
      { eapply c2h_iftab_keep; [exact HIF2 | exact HIFP2 | exact KIF | exact MU2 | c2h_dj2 ..]. }
      split; [rewrite KO, HO2; exact KO0|].
      split; [rewrite KMI, HMI2; exact KM0|].
      split; [rewrite KOD, KCL, HOD2, HCL2; exact KOC0|].
      split; [rewrite KOD, HOD2; exact KOP0|].
      split; [rewrite KNX; exact HN2 | exact KNS]. }
    split; [split; [exact K9 | exact HMKwf]|].
    split; [split; [exact HM3 | exact ML]|].
    split; [exact MW|]. split; [exact MA|].
    split; [|exact MNR].
    unfold md_kstate, nk_kstate. rewrite MNX, MSO, MSE, KNX, HN2, KSO, KSE. reflexivity.
  - exists (c2h_W S md). split; [exact MUA|]. split; [exact WMA|].
    intros x Hx HO. destruct (c2h_not_outside _ _ HO) as (lo & hi & Hin & Hr).
    unfold c2h_W in Hin. cbn [In] in Hin.
    repeat destruct Hin as [Ein|Hin]; try contradiction; injection Ein as <- <-;
      unfold own_w, c2_hp; cbn [e_S e_md e_mk];
      unfold A_G_NL, NK_SIZE, NK_OPEN, NK_CHUNK, A_G_NAMES, G_NAMES_SIZE, A_LONG_ALIAS, LONG_ALIAS_SIZE,
        SLOT_STACK_Z, MD_SIZE, A_ERRNO, A_TP, ERRNO_TP_OFF in *;
      first [ left; lia | right; left; lia | right; right; right; left; lia
            | right; right; right; right; right; exists md, 8856; split; [left; reflexivity | lia] ].
Qed.

(* ==========================================================================
   4. The segment
   ========================================================================== *)

Ltac c2h_curm := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => mm end.

(* the read of the 32-bit field at A + off = a of the byte block at A *)
Ltac c2h_rd4 A off a :=
  let mm := c2h_curm in
  lazymatch goal with
  | HU : u8arr rsegs mm A ?b, HL : Z.of_nat (length ?b) = ?n |- _ =>
      let HR := fresh "HR" in
      pose proof (c2h_u8arr_rd32 mm A b off a HU ltac:(lia) ltac:(lia) ltac:(lia)) as HR
  end.

Ltac c2h_sok4 A off a :=
  let mm := c2h_curm in
  lazymatch goal with
  | HU : u8arr rsegs mm A ?b, HL : Z.of_nat (length ?b) = ?n |- _ =>
      let HS := fresh "HS" in
      pose proof (c2h_u8arr_store_ok mm A b off a 4 HU ltac:(lia) ltac:(lia) ltac:(lia)) as HS
  end.

Lemma c2h_u8arr_write4 : forall m A bs off a (v : word) n,
  u8arr rsegs m A bs -> Z.of_nat (length bs) = n -> 0 <= off -> off + 4 <= n -> a = A + off ->
  u8arr rsegs (write_to_mem m (Z_to_bv 64 a) (le4 v)) A (upd_bytes bs (Z.to_nat off) (le4 v)) /\
  Z.of_nat (length (upd_bytes bs (Z.to_nat off) (le4 v))) = n.
Proof.
  intros m A bs off a v n HU HL H0 H4 Ea. split.
  - apply c2h_u8arr_write; [exact HU | exact H0 | rewrite length_le4; lia | exact Ea].
  - rewrite upd_bytes_length by (rewrite length_le4; lia). exact HL.
Qed.

(* after a 4-byte store into the block at A: the block's new bytes, then every other fact moved *)
Ltac c2h_st4 A off :=
  lazymatch goal with
  | |- evt ?segs _ (MS _ _ _ _ _ (write_to_mem ?mm (Z_to_bv 64 ?a) (le4 ?v)) _) =>
    lazymatch goal with
    | HU : u8arr rsegs mm A ?b, HL : Z.of_nat (length ?b) = ?n |- _ =>
        let HU' := fresh "HU" in let HL' := fresh "HL" in
        destruct (c2h_u8arr_write4 mm A b off a v n HU HL ltac:(lia) ltac:(lia) ltac:(lia)) as [HU' HL'];
        clear HL;
        change (write_to_mem mm (Z_to_bv 64 a) (le4 v)) with (write_to_mem mm (wa a) (le4 v)) in *;
        lazymatch goal with HI : mem_inv segs mm |- _ =>
          apply (mem_inv_store segs mm (wa a) (le4 v)) in HI;
          [| rewrite length_le4; match goal with HS : store_ok _ mm _ 4 = true |- _ => exact HS end ]
        end;
        transport_chunks segs mm a (le4 v);
        footprint_after_store segs mm a (le4 v);
        let m' := fresh "m" in
        remember (write_to_mem mm (wa a) (le4 v)) as m' eqn:Hm'; clear Hm'
    end
  end.

Section H2.
Hypothesis KERNEL_OK : kernel_contract.

Lemma c2h_head2 : forall (E : lenv) (i : Z) (gp : word) (s : Z) (ms : machine_state),
  lenv_ok E -> c2h_13d48 E i gp s ms ->
  evt rsegs (c2_post E (ms_mem ms) (fun c => exists s, c2_13d70 E i gp s c)) ms.
Proof.
  intros [S md mk p0 pl sv] i gp s ms HE HC.
  destruct HC as (ra & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s3 & s4 & t3 & t4 & t5 & t6 & F & fc
                  & m & P & N & j0 & j1 & j2 & kbs & mbs & gbs & Ems & FRM & Hi & Hs & HFR & K0 & HCUR & HNK & KF
                  & HIF & HLA & HMD & HMDwf & HMKwf & HMA & MI & TM & ST).
  assert (Em : ms_mem ms = m) by (rewrite Ems; reflexivity).
  rewrite Em. subst ms. cbn [e_S e_md e_mk e_p0 e_pl e_saved] in *.
  pose proof HE as HE'. unfold lenv_ok in HE'. cbn [e_S e_md e_mk e_p0 e_pl e_saved] in HE'.
  destruct HE' as (HS1 & HS2 & HS3 & BMD & BMK & Hmd16 & Hmk16 & Hmdmk & Hpl1 & BPL & Hplmd & Hplmk & Hsv).
  destruct (c2h_blk_where S md MD_SIZE ltac:(unfold MD_SIZE; lia) BMD) as (Hmd1 & Hmd2 & Hmdw).
  destruct (c2h_blk_where S p0 (Z.of_nat (length pl)) ltac:(lia) BPL) as (Hp01 & Hp02 & _).
  clear BMD BMK BPL Hmdmk Hplmd Hplmk Hmd16 Hmk16 HS3.
  unfold SLOT_STACK_Z, MD_SIZE in HS1, Hmd2, Hp02, Hmdw.
  pose proof HCUR as (k & Hk & EP & EN). cbn [e_p0 e_pl] in Hk, EP, EN.
  unfold c2_frame in HFR. cbn [e_S e_md e_mk] in HFR.
  destruct (c2h_frame_split _ _ _ _ _ _ _ _ _ HFR) as (FH & FC & FT). clear HFR.
  pose proof HMD as [HMDu HMDl].
  pose proof (munch_refl (c2h_W S md) m) as MUA. pose proof (wmono_refl rsegs m) as WMA.
  unfold c2h_W, A_G_NL, NK_CHUNK, NK_OPEN, A_LONG_ALIAS, LONG_ALIAS_SIZE in MUA.
  unfold MD_SIZE in HMDl.
  pose proof K0 as (_ & _ & _ & _ & _ & K6 & _).
  unfold c2h_fhead, wz, SLOT_FRAME, SLOT_STACK_Z, L_LH, A_TP, GNL40, GNL42, A_JT, A_G_NL, MD_N_REQ, A_ODD,
    A_EMPTY, A_G_NAMES, MD_MARK in FH, FC, FT, ST |- *.
  (* 0x13d48 addi a0, sp, 0x40; 0x13d4c jal kernel *)
  step. step.
  unfold c2_post.
  lazymatch goal with |- evt _ _ (MS ?R _ _ _ _ _ _) =>
    assert (SP : spZ R = S - 480)
      by (change (spZ R) with (bv_unsigned (Z_to_bv 64 (S - 480))); apply unsigned_lit; lia);
    assert (A0 : arg R 0 = S - 480 + 64)
      by (change (arg R 0) with (bv_unsigned (Z_to_bv 64 (S - 480 + 64))); apply unsigned_lit; lia);
    assert (KR : c2h_kregs R) by (unfold c2h_kregs; rewrite SP, A0; lia)
  end.
  eapply (c2h_leaf_run _ _ _ _ _ _ KERNEL_OK) with (lo := S - 65536).
  - cbv beta. eapply c2h_kpre; [exact HE | exact KR | exact A0 | exact FC | exact K0 | exact HCUR
                               | exact HNK | exact (proj1 KF) | exact HIF | exact HLA | exact MI].
  - exact MI.
  - rewrite unsigned_lit by lia. exact ST.
  - rewrite unsigned_lit by lia. lia.
  - rewrite unsigned_lit by lia. lia.
  - intros regs' m2 MU1 WM1 MI1 ST1 PO.
    cbv beta in MU1, PO.
    rewrite (unsigned_lit (S - 480)) in MU1, ST1 by lia.
    lazymatch type of MU1 with context [arg ?R' 0] =>
      assert (A0' : arg R' 0 = S - 480 + 64)
        by (change (arg R' 0) with (bv_unsigned (Z_to_bv 64 (S - 480 + 64))); apply unsigned_lit; lia)
    end.
    rewrite A0' in MU1, PO.
    destruct (PO kbs HNK) as (kbs2 & HNK2 & HNK2wf & Hnext2 & Hnch2 & Hend2 & Hsock2 & Hsend2 & Hopen2 & Hopened2
                              & Hclosed2 & Hmis2 & Hnsent2 & Hsent2 & Hnif2 & HIF2 & HCUR2 & (la2 & HLA2)).
    clear Hnch2 Hend2 Hsock2 Hsend2 Hsent2.
    assert (UP : bv_unsigned (Z_to_bv 64 P) = P) by (apply unsigned_lit; lia).
    assert (UN : bv_unsigned (Z_to_bv 64 N) = N) by (apply unsigned_lit; lia).
    destruct (HCUR2 (Z_to_bv 64 P) (Z_to_bv 64 N) FC) as (adv & Hadv & FC2).
    rewrite UN in Hadv. rewrite UP, UN in FC2.
    pose proof (HIF2 link_tab HIF) as HIF3.
    clear PO HCUR2 HIF2.
    unfold A_G_NL, NK_CHUNK, NK_OPEN, A_LONG_ALIAS, LONG_ALIAS_SIZE in MU1.
    transport_after_call rsegs m m2 MU1 WM1.
    clear MU1 WM1.
    assert (IFP2 : ifptrs_at m2) by (eapply c2h_ifptrs_keep; [exact K6 | exact MUA | c2h_dj2]).
    destruct HNK2 as [HNK2u HNK2l]. unfold A_G_NL, NK_SIZE in HNK2u, HNK2l.
    assert (LK2 : NK_SIZE = Z.of_nat (length kbs2)) by (rewrite HNK2l; reflexivity).
    unfold A_LONG_ALIAS in HLA2.
    pose proof (munch_refl (c2h_Ws md) m2) as MU2. unfold c2h_Ws in MU2.
    pose proof (wmono_refl rsegs m2) as WM2.
    replace (ret_pc (Z_to_bv 64 81232)) with (Z_to_bv 64 81232) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
    (* model_begin, 0x13d50 - 0x13d6c *)
    c2h_rd4 203648 262668 466316. step.
    c2h_sok4 md 0 md. step. c2h_st4 md 0.
    c2h_rd4 203648 262672 466320. step.
    c2h_sok4 md 8 (md + 8). step. c2h_st4 md 8.
    c2h_sok4 md 4 (md + 4). step. c2h_st4 md 4.
    c2h_sok4 md 8336 (md + 8336). step. c2h_st4 md 8336.
    step.
    c2h_sok4 203648 271016 474664. step. c2h_st4 203648 271016.
    apply evt_done.
    lazymatch goal with
    | HK : u8arr rsegs _ 203648 ?kb, HM : u8arr rsegs _ md ?mb |- _ =>
        eapply (c2h_h2_fin S md mk p0 pl sv i gp s) with (kb3 := kb) (mb3 := mb) (m2 := m2)
    end;
      [ exact HE | exact K0 | exact TM | exact KF | exact HMDwf | exact HMKwf | exact HMA | exact (proj2 HMD)
      | exact HNK2wf | exact (eq_sym LK2) | exact Hnext2 | exact Hopen2 | exact Hopened2 | exact Hclosed2 | exact Hmis2
      | exact HIF3 | exact IFP2 | exact MU2 | exact MUA | exact WMA | eassumption | reflexivity | eassumption
      | reflexivity | reflexivity | reflexivity | exact HLA2 | exact FH | exact FC2 | exact FT | exact MI1
      | exact ST1 | exact Hk | exact EP | exact EN | exact Hadv | exact FRM | exact Hi | exact Hs ].
Qed.

End H2.
