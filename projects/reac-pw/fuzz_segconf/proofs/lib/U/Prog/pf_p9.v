(** reac_segconf_parse_file, piece P9 (UBSan build, image 1696d6c34ffd): the shared sites, proof of
    lib/U/Prog/reac_segconf_parse_file_pieces_c.S_P9 from the contracts of refuse (U/Prog/refuse_c.v) and snprintf
    (U/Prog/snprintf_c.v).

    Code (the UBSan binary):
    - OUTS 0x15688: a2 = F_outside (0x10402), a0 = c (the slot sp + 0x90), a1 = s3, a3 = s8 (the key), falls into HREF.
    - HREF 0x1569c: `jal refuse` (0x15c80), which returns to CLR.
    - CLR 0x156a0: `sd zero,0x88(sp)` (cur = NULL), falls into TAIL (0x156a4).
    - KNOCK 0x158e8: a2 = F_knock (0x10762), falls into KREF. KREF 0x158f0: a3 = sp + 0x3a8 (cur_name), a0 = c (the
      slot sp + 0x90), a1 = s3, a4 = s7, falls into NOKEY. NOKEY 0x15900: `jal refuse`, then `j` TAIL (0x15904).
    - PROV 0x15b70: a1 = 96, falls into PROVM. PROVM 0x15b74: a3 = c->reading (the slot sp + 0x50), falls into CNAME.
      CNAME 0x15b78: `jal snprintf` (0x19a14), then `j` TAIL (0x15b7c).
    No trap. The structure is the plain twin's (lib/Prog/pf_p9.v); cur lives in the frame slot sp + 0x88
    (pf_curslot), kept by every call here (U/Prog/pfC_facts.pfc_curslot_call) and set to NULL by CLR. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Image Bytes ZBridge FP.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U Require MemNorm.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require Import printf_facts_c snprintf_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec seg_spec pf_pieces_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require Import seg_env refuse_c reac_segconf_parse_file_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require Import reac_segconf_parse_file_pieces_c pfC_facts.
Import ListNotations.
Open Scope Z_scope.

Section P9U.
Hypothesis REF : refuse_contract.
Hypothesis SNP : snprintf_contract.

(** The refusal formats of the site 0x15900 (two %s each: cur_name and the value or the key). *)
Definition P9_FMTS : list (list Z * Z) :=
  [(F_knock, PF_STR_KNOCK); (F_badrole, PF_STR_BADROLE); (F_badignore, PF_STR_BADIGNORE); (F_nokey, PF_STR_NOKEY)].

Lemma p9_fmts : forall f fp, In (f, fp) P9_FMTS -> In (f, fp) PFC_FMTS /\ conv_kinds f = [true; true].
Proof.
  intros f fp H. unfold P9_FMTS, PFC_FMTS in *.
  destruct H as [E|[E|[E|[E|[]]]]]; injection E as <- <-; (split; [cbn [In]; tauto | vm_compute; reflexivity]).
Qed.

(** The refusal formats of the site 0x1569c (one %s each). *)
Definition P9_HFMTS : list (list Z * Z) :=
  [(F_notclosed, PF_STR_NOTCLOSED); (F_after, PF_STR_AFTER); (F_unknown, PF_STR_UNKNOWN); (F_outside, PF_STR_OUTSIDE)].

Lemma p9_hfmt_at : forall m f fp, mem_inv rsegs m -> In (f, fp) P9_HFMTS ->
  fp <> 0 /\ cstrz_at rsegs m fp f /\ RO_LO <= fp /\ fp + Z.of_nat (length f) + 1 <= sa_ro_end SA /\
  In f REFUSE_FORMATS /\ conv_kinds f = [true].
Proof.
  intros m f fp MI Hin. unfold P9_HFMTS in Hin.
  destruct Hin as [E|[E|[E|[E|[]]]]]; injection E as E1 E2; subst f fp;
    (split; [unfold PF_STR_NOTCLOSED, PF_STR_AFTER, PF_STR_UNKNOWN, PF_STR_OUTSIDE; lia|]);
    (split; [match goal with |- cstrz_at _ _ _ ?F => exists (zb F) end;
             split; [apply pfc_ro_str; [exact MI | pfc_zle | pfc_zle | vm_compute; reflexivity]
                    |split; [vm_compute; reflexivity | apply nulfree_forallb; vm_compute; reflexivity]]|]);
    (split; [pfc_zle|]); (split; [pfc_zle|]);
    (split; [unfold REFUSE_FORMATS; cbn [In]; auto 20 | vm_compute; reflexivity]).
Qed.

(** The refuse site 0x15900 with its arguments in a0 .. a4. *)
Lemma p9_site : forall n, H_TAIL n ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (v : pf_sv)
         (c t : Z) (s : list Z) (rc : rconf) (cur : option nat) (nm : list Z) (o : nat) (ln : Z) (d : list (list Z))
         (f : list Z) (fp xp : Z) (x : list Z),
    pf_ctx m fc (bv_unsigned sp) lo v c t s o ln d n ->
    pf_state m (bv_unsigned sp) c rc cur nm (length (skipn o s)) ->
    pf_regs s0 s1 s2 s3 s5 s10 s11 (t + Z.of_nat (pf_next s o)) (ln + 1) ->
    pf_curslot m (bv_unsigned sp) c cur ->
    In (f, fp) P9_FMTS ->
    a0 = Z_to_bv 64 c ->
    a1 = Z_to_bv 64 (ln + 1) ->
    a2 = Z_to_bv 64 fp ->
    a3 = Z_to_bv 64 (bv_unsigned sp + PF_NAMEBUF) ->
    a4 = Z_to_bv 64 xp ->
    cstr_at rsegs m xp x ->
    pf_inb (bv_unsigned sp + PF_BUF) xp x ->
    evt rsegs
      (pf_fin v sp gp tp F m lo c
         (r_lines (refuse rc (ln + 1) f [AS nm; AS x], cur, nm) (ln + 1) (lines (skipn (pf_next s o) s))))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PF_PC_NOKEY) fc None m (seg_rom rsegs)).
Proof.
  intros n HT ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo v c t s rc cur nm o ln d f fp xp x HCTX HST HREGS HCS HIN -> -> -> -> -> HX HXB.
  destruct (p9_fmts f fp HIN) as [HIN' HCK].
  pose proof HCTX as (HENV & HTXT & _ & Ho & _ & (_ & _ & Ld & Lln)).
  pose proof HST as (HRC & _ & HNM & _).
  destruct (pfc_env_lo _ _ _ _ _ _ HENV) as (Lo0 & Lsp & Lhi & Hap & Lie & Lsp63).
  pose proof HENV as (_ & _ & _ & _ & _ & _ & _ & MI & _).
  destruct (pfc_fmt_at m f fp MI HIN') as (Hfp & HF & HR1 & HR2 & HFR).
  pose proof (pfc_env_al _ _ _ _ _ _ HENV) as Hal.
  destruct (pfc_nm_cstr m (bv_unsigned sp) nm HNM Hal) as [HNC HNL].
  pose proof HRC as (cbs & HCB & (HCL & _)).
  pose proof (bytes_at_bound _ _ _ _ HCB) as HCBB.
  pose proof (pfc_next_gt s o Ho) as [G1 G2].
  pose proof HTXT as (_ & _ & Hsl & _). pose proof (pfc_len65535 s Hsl) as Hsl'.
  destruct HXB as [HXB1 HXB2].
  assert (Hfpr : 0 <= fp < 2 ^ 64) by (unfold RO_LO in HR1; cbn [sa_ro_end SA SEG_UBSAN] in HR2; lia).
  assert (Hcr : 0 <= c < 2 ^ 64) by (unfold SEG_C_SIZE in *; lia).
  assert (Hlnr : 0 <= ln + 1 < 2 ^ 64) by lia.
  (* 0x15900: jal refuse *)
  unfold PF_PC_NOKEY. zstep.
  eapply evt_cut.
  { eapply REF with (lo := lo) (rc := rc) (ln := ln + 1) (f := f) (args := [AS nm; AS x]).
    rewrite (unsigned_lit c), (unsigned_lit (ln + 1)), (unsigned_lit fp) by lia.
    eapply pfc_refuse_pre; [exact HCTX | exact HST | exact HFR | exact HCK | exact Hfp | exact HF | exact HR1
                           | exact HR2 |].
    cbn [va_args_ok]. split; [|split; [|exact I]].
    - apply (pfc_va_frame m fc (bv_unsigned sp) lo c v rc); auto;
        unfold PF_NAMEBUF, PARSE_FILE_FRAME in *; first [lia | apply pfc_le65535; lia].
    - apply (pfc_va_frame m fc (bv_unsigned sp) lo c v rc); auto;
        unfold PF_BUF, PARSE_FILE_FRAME in *; first [lia | apply pfc_le65535; lia]. }
  intros ms' POST. unfold ret_void_fp in POST.
  destruct POST as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' &
                    F' & fc' & m' & E & FRM & HF' & MU & WM & MI' & TM' & ST' & HRC').
  subst ms'. rewrite (unsigned_lit c) in MU, HRC' by lia.
  rewrite ret_pc_even by (try lia; reflexivity).
  (* 0x15904: j TAIL *)
  zstep.
  destruct (pfc_after_refuse m m' fc fc' (bv_unsigned sp) lo v c t s o ln d n rc cur nm f [AS nm; AS x]
              HCTX HST MU WM ST' MI' TM' FRM HRC') as (HH & HS' & Hn' & MU').
  assert (HCS' : pf_curslot m' (bv_unsigned sp) c cur).
  { apply (pfc_curslot_call m m' fc (bv_unsigned sp) lo c v cur _ HENV HCS MU).
    intros y Hy. destruct (pfc_outside_dec (refuse_W (bv_unsigned sp) c rc) y) as [Q|Q]; [exact Q|].
    exfalso. destruct (pfc_refuse_W_low m fc (bv_unsigned sp) lo c v rc HENV HRC y Q);
      unfold apart, SEG_C_SIZE, PF_CURSLOT in *; lia. }
  eapply evt_mono.
  { eapply HT; [exact HH | exact HS' | exact Hn' | exact HREGS | exact HCS']. }
  intros ms Hp. eapply pf_fin_weaken; [exact Hp | exact MU' | exact WM | exact HF'].
Qed.

(** A register the code set from a loop register, a frame slot or sp: equal to the cut's value. *)
Ltac p9_eq := first [ reflexivity | rewrite unsigned_lit by lia; f_equal; lia | f_equal; lia ].

(** The site 0x158f0 (KREF's pc): a2 holds the format; a3, a0, a1, a4 are set from sp, the c slot, s3, s7. *)
Lemma p9_kref_gen : forall n, H_TAIL n ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (v : pf_sv)
         (c t : Z) (s : list Z) (rc : rconf) (cur : option nat) (nm : list Z) (o : nat) (ln : Z) (d : list (list Z))
         (f : list Z) (fp vp : Z) (x : list Z),
    pf_ctx m fc (bv_unsigned sp) lo v c t s o ln d n ->
    pf_state m (bv_unsigned sp) c rc cur nm (length (skipn o s)) ->
    pf_regs s0 s1 s2 s3 s5 s10 s11 (t + Z.of_nat (pf_next s o)) (ln + 1) ->
    pf_curslot m (bv_unsigned sp) c cur ->
    In (f, fp) P9_FMTS ->
    a2 = Z_to_bv 64 fp ->
    s7 = Z_to_bv 64 vp ->
    cstr_at rsegs m vp x ->
    pf_inb (bv_unsigned sp + PF_BUF) vp x ->
    evt rsegs
      (pf_fin v sp gp tp F m lo c
         (r_lines (refuse rc (ln + 1) f [AS nm; AS x], cur, nm) (ln + 1) (lines (skipn (pf_next s o) s))))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PF_PC_KREF) fc None m (seg_rom rsegs)).
Proof.
  intros n HT ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo v c t s rc cur nm o ln d f fp vp x HCTX HST HREGS HCS HIN -> -> HX HXB.
  pose proof HCTX as (_ & _ & HSPL & Ho & _ & (_ & _ & Ld & Lln)).
  pose proof HST as (HRC & _).
  pose proof HRC as (cbs & HCB & (HCL & _)). pose proof (bytes_at_bound _ _ _ _ HCB) as HCBB.
  pose proof (pfc_next_gt s o Ho) as [G1 G2].
  pose proof HCTX as (_ & (_ & _ & Hsl & _) & _). pose proof (pfc_len65535 s Hsl) as Hsl'.
  assert (Hcr : 0 <= c < 2 ^ 64) by (unfold SEG_C_SIZE in *; lia).
  assert (Hlnr : 0 <= ln + 1 < 2 ^ 64) by lia.
  pose proof (pfc_ld_c m (bv_unsigned sp) c HSPL) as HLD.
  pose proof HREGS as (-> & -> & -> & -> & -> & -> & ->).
  unfold PF_PC_KREF, PF_CSLOT in *. do 4 zstep.
  eapply p9_site; [exact HT | exact HCTX | exact HST | exact HREGS | exact HCS | exact HIN
                  | p9_eq | p9_eq | reflexivity | p9_eq | p9_eq | exact HX | exact HXB].
Qed.

Lemma p9_nokey : forall n, H_TAIL n -> H_NOKEY n.
Proof.
  intros n HT. unfold H_NOKEY. intros. eapply p9_site; try eassumption.
  unfold P9_FMTS. right; right; right; left; reflexivity.
Qed.

Lemma p9_kref : forall n, H_TAIL n -> H_KREF n.
Proof.
  intros n HT. unfold H_KREF. intros until x. intros HCTX HST HREGS HCS HIN Ha2 Hs7 HX HXB.
  eapply p9_kref_gen; try eassumption.
  unfold P9_FMTS. destruct HIN as [E|[E|[]]]; injection E as <- <-; [right; left | right; right; left]; reflexivity.
Qed.

Lemma p9_knock : forall n, H_TAIL n -> H_KNOCK n.
Proof.
  intros n HT. unfold H_KNOCK. intros until x. intros HCTX HST HREGS HCS Hs7 HX HXB.
  unfold PF_PC_KNOCK. do 2 zstep.
  eapply p9_kref_gen with (f := F_knock) (fp := PF_STR_KNOCK); try eassumption; [| reflexivity].
  unfold P9_FMTS. left; reflexivity.
Qed.

Lemma p9_not_out1 : forall a b x, ~ outside [(a, b)] x -> a <= x < b.
Proof.
  intros a b x H. cbn [outside] in H.
  destruct (Z_le_dec a x) as [Q1|Q1]; destruct (Z_lt_dec x b) as [Q2|Q2]; try (split; assumption);
    exfalso; apply H; (split; [lia | exact I]).
Qed.

(** CLR 0x156a0 from a tail context whose cur slot is not known: `sd zero,0x88(sp)` (cur = NULL), then TAIL. *)
Lemma p9_clr_gen : forall n, H_TAIL n ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (v : pf_sv)
         (c t : Z) (s : list Z) (rc : rconf) (nm : list Z) (o : nat) (ln : Z) (d : list (list Z)),
    pf_hctx m fc (bv_unsigned sp) lo v c t s o ln d ->
    pf_state m (bv_unsigned sp) c rc None nm (length (skipn o s)) ->
    (length (skipn o s) < n)%nat ->
    pf_regs s0 s1 s2 s3 s5 s10 s11 (t + Z.of_nat o) ln ->
    evt rsegs
      (pf_fin v sp gp tp F m lo c (r_lines (rc, None, nm) ln (lines (skipn o s))))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PF_PC_CLR) fc None m (seg_rom rsegs)).
Proof.
  intros n HT ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo v c t s rc nm o ln d HH HST Hn HREGS.
  pose proof HH as (HENV & HTXT & HSPL & HL & HSUF).
  pose proof HST as (HRC & Hcur & HNM & Hcnt).
  destruct (pfc_env_lo _ _ _ _ _ _ HENV) as (Lo0 & Lsp & Lhi & Hap & Lie & Lsp63).
  pose proof HENV as (_ & _ & _ & _ & (_ & HTM0 & _) & _ & (ST & _) & MI & _).
  pose proof (proj1 (stk_split rsegs m lo (bv_unsigned sp) (bv_unsigned sp + PARSE_FILE_FRAME) ST
                       ltac:(unfold PARSE_FILE_FRAME; lia))) as STL.
  destruct (pfc_dst_stk m lo (bv_unsigned sp + PARSE_FILE_FRAME) (bv_unsigned sp + 136) 8 ST
              ltac:(lia) ltac:(unfold PARSE_FILE_FRAME; lia) ltac:(lia)) as (junk & SLOT).
  change (Z.to_nat 8) with 8%nat in SLOT.
  pose proof (munch_refl [(bv_unsigned sp + 136, bv_unsigned sp + 144)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof ST as ST0.
  pose proof (conj ST0 (conj HH HST)) as KEEP. clear ST0 HH HST HENV HTXT HSPL HSUF HRC HNM.
  unfold PF_PC_CLR. zstep.
  match goal with H : rw_cells _ ?mm _ _ |- _ => rename mm into m' end.
  destruct KEEP as (ST0 & HH & HST).
  set (W := [(bv_unsigned sp + 136, bv_unsigned sp + 144)]) in *.
  assert (HCS' : pf_curslot m' (bv_unsigned sp) c None).
  { unfold pf_curslot, PF_CURSLOT. cbn [pf_cur_ptr].
    match goal with H : rw_cells _ m' _ _ |- _ => destruct H as [[_ HB] _] end.
    cbn [cells_bytes cbytes] in HB. rewrite app_nil_r in HB.
    rewrite ?w0_lit in HB. exact HB. }
  assert (PR : forall y, pfc_scr (bv_unsigned sp) y -> ~ outside W y -> exists b, mrd rsegs m' (wa y) = Some b).
  { intros y Hy Hw. unfold pf_curslot, PF_CURSLOT in HCS'. apply (pfc_bytes_mrd m' _ _ y HCS').
    rewrite length_le8. unfold W in Hw. cbn [outside] in Hw. lia. }
  pose proof HH as (HENV & HTXT & HSPL & _ & _).
  pose proof HST as (HRC & _ & HNM & _).
  assert (FW : pfc_fw (bv_unsigned sp) lo c W).
  { intros y Hy. right; right. unfold W in Hy. cbn [outside] in Hy. unfold pfc_scr, PF_CURSLOT. lia. }
  assert (TM' : MemNorm.task_mem rsegs m').
  { apply (pfc_task_mem_munch W m m' HTM0 MU). intros y Hy. unfold W in Hy.
    pose proof (p9_not_out1 _ _ _ Hy) as Hy'.
    destruct ST0 as (_ & _ & STa).
    destruct (STa (bv_unsigned y) ltac:(unfold PARSE_FILE_FRAME; lia)) as [_ (b & Hb)].
    unfold wa in Hb. rewrite Z_to_bv_bv_unsigned in Hb. rewrite Hb. discriminate. }
  assert (HENV' : pf_env m' fc (bv_unsigned sp) lo c v).
  { eapply pfc_env_call; [exact HENV | exact MU | exact WM | exact FW | exact PR | | | exact TM' |].
    - match goal with H : stk _ m' lo (bv_unsigned sp) |- _ => exact H end.
    - match goal with H : mem_inv _ m' |- _ => exact H end.
    - pose proof HENV as (_ & _ & _ & _ & (Hfrm & _) & _). exact Hfrm. }
  assert (HTXT' : pf_text m' (bv_unsigned sp) lo c t s)
    by (apply (pfc_text_call m m' (bv_unsigned sp) lo c t s W HTXT MU FW); lia).
  assert (HH' : pf_hctx m' fc (bv_unsigned sp) lo v c t s o ln d).
  { split; [exact HENV'|]. split; [exact HTXT'|].
    split; [exact (pfc_spill_call m m' fc (bv_unsigned sp) lo c v W HENV HSPL MU FW)|]. split; [exact HL|].
    destruct HTXT' as (_ & HC & _). apply pfc_cstr_skipn; [exact HC | exact (proj1 HL)]. }
  assert (HST' : pf_state m' (bv_unsigned sp) c rc None nm (length (skipn o s))).
  { split; [|split; [exact I | split; [|exact Hcnt]]].
    - apply (pfc_rconf_munch W m m' c rc HRC MU). intros y Hy. unfold W, apart, SEG_C_SIZE, PARSE_FILE_FRAME in *.
      cbn [outside]. repeat split; lia.
    - apply (pfc_nm_call m m' fc (bv_unsigned sp) lo c v nm W HENV HNM MU). intros y Hy. unfold W, PF_NAMEBUF, PF_SAVE in *.
      cbn [outside]. repeat split; lia. }
  eapply evt_mono.
  { eapply HT; [exact HH' | exact HST' | exact Hn | exact HREGS | exact HCS']. }
  intros ms Hp. eapply pf_fin_weaken; [exact Hp | | exact WM | intros; reflexivity].
  apply (munch_weaken W _ m m'); [|exact MU]. intros y Hy. unfold pfc_W, RC_PARSE_W, PARSE_FILE_STACK,
    REFUSE_STACK, PRINTF_K, PARSE_FILE_FRAME, W in *. cbn [outside] in *. repeat split; lia.
Qed.

Lemma p9_clr : forall n, H_TAIL n -> H_CLR n.
Proof.
  intros n HT. unfold H_CLR. intros until d. intros HCTX HST HREGS.
  destruct (pfc_hctx_next m fc (bv_unsigned sp) lo v c t s o ln d n HCTX) as (HH & _ & Hn').
  eapply p9_clr_gen; [exact HT | exact HH | exact HST | exact Hn' | exact HREGS].
Qed.

(** HREF 0x1569c: refuse(c, lineno, f, x) with one %s, then CLR. *)
Lemma p9_href : forall n, H_TAIL n -> H_HREF n.
Proof.
  intros n HT. unfold H_HREF.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo v c t s rc nm o ln d f fp xp x HCTX HST HREGS HIN -> -> -> -> HX HXB.
  pose proof HCTX as (HENV & HTXT & _ & Ho & _ & (_ & _ & Ld & Lln)).
  pose proof HST as (HRC & _ & HNM & _).
  destruct (pfc_env_lo _ _ _ _ _ _ HENV) as (Lo0 & Lsp & Lhi & Hap & Lie & Lsp63).
  pose proof HENV as (_ & _ & _ & _ & _ & _ & _ & MI & _).
  destruct (p9_hfmt_at m f fp MI HIN) as (Hfp & HF & HR1 & HR2 & HFR & HCK).
  pose proof HRC as (cbs & HCB & (HCL & _)).
  pose proof (bytes_at_bound _ _ _ _ HCB) as HCBB.
  pose proof (pfc_next_gt s o Ho) as [G1 G2].
  pose proof HTXT as (_ & _ & Hsl & _). pose proof (pfc_len65535 s Hsl) as Hsl'.
  destruct HXB as [HXB1 HXB2].
  assert (Hfpr : 0 <= fp < 2 ^ 64) by (unfold RO_LO in HR1; cbn [sa_ro_end SA SEG_UBSAN] in HR2; lia).
  assert (Hcr : 0 <= c < 2 ^ 64) by (unfold SEG_C_SIZE in *; lia).
  assert (Hlnr : 0 <= ln + 1 < 2 ^ 64) by lia.
  (* 0x1569c: jal refuse *)
  unfold PF_PC_HREF. zstep.
  eapply evt_cut.
  { eapply REF with (lo := lo) (rc := rc) (ln := ln + 1) (f := f) (args := [AS x]).
    rewrite (unsigned_lit c), (unsigned_lit (ln + 1)), (unsigned_lit fp) by lia.
    eapply pfc_refuse_pre; [exact HCTX | exact HST | exact HFR | exact HCK | exact Hfp | exact HF | exact HR1
                           | exact HR2 |].
    cbn [va_args_ok]. split; [|exact I].
    apply (pfc_va_frame m fc (bv_unsigned sp) lo c v rc); auto;
      unfold PF_BUF, PARSE_FILE_FRAME in *; first [lia | apply pfc_le65535; lia]. }
  intros ms' POST. unfold ret_void_fp in POST.
  destruct POST as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' &
                    F' & fc' & m' & E & FRM & HF' & MU & WM & MI' & TM' & ST' & HRC').
  subst ms'. rewrite (unsigned_lit c) in MU, HRC' by lia.
  rewrite ret_pc_even by (try lia; reflexivity).
  destruct (pfc_after_refuse m m' fc fc' (bv_unsigned sp) lo v c t s o ln d n rc None nm f [AS x]
              HCTX HST MU WM ST' MI' TM' FRM HRC') as (HH & HS' & Hn' & MU').
  eapply evt_mono.
  {
    eapply p9_clr_gen; [exact HT | exact HH | exact HS' | exact Hn' | exact HREGS]. }
  intros ms Hp. eapply pf_fin_weaken; [exact Hp | exact MU' | exact WM | exact HF'].
Qed.

Lemma p9_outs : forall n, H_TAIL n -> H_OUTS n.
Proof.
  intros n HT. unfold H_OUTS. intros until key. intros HCTX HST HREGS HCS Hs8 HX HXB.
  pose proof HCTX as (_ & _ & HSPL & Ho & _ & (_ & _ & Ld & Lln)).
  pose proof HST as (HRC & _).
  pose proof HRC as (cbs & HCB & (HCL & _)). pose proof (bytes_at_bound _ _ _ _ HCB) as HCBB.
  pose proof (pfc_next_gt s o Ho) as [G1 G2].
  pose proof HCTX as (_ & (_ & _ & Hsl & _) & _). pose proof (pfc_len65535 s Hsl) as Hsl'.
  assert (Hcr : 0 <= c < 2 ^ 64) by (unfold SEG_C_SIZE in *; lia).
  assert (Hlnr : 0 <= ln + 1 < 2 ^ 64) by lia.
  pose proof (pfc_ld_c m (bv_unsigned sp) c HSPL) as HLD.
  pose proof HREGS as (-> & -> & -> & -> & -> & -> & ->). subst s8.
  unfold PF_PC_OUTS, PF_CSLOT in *. do 5 zstep.
  eapply p9_href with (f := F_outside) (fp := PF_STR_OUTSIDE);
    [exact HT | exact HCTX | exact HST | exact HREGS | | p9_eq | p9_eq | reflexivity | reflexivity | exact HX | exact HXB].
  unfold P9_HFMTS. right; right; right; left; reflexivity.
Qed.

Lemma p9_not_out2 : forall a b a' b' x, ~ outside [(a, b); (a', b')] x -> a <= x < b \/ a' <= x < b'.
Proof.
  intros a b a' b' x H. cbn [outside] in H.
  destruct (Z_le_dec a x); destruct (Z_lt_dec x b); destruct (Z_le_dec a' x); destruct (Z_lt_dec x b');
    try (left; split; assumption); try (right; split; assumption);
    exfalso; apply H; (split; [lia | split; [lia | exact I]]).
Qed.

(** The provenance write at 0x15b78: snprintf(seg[gi] + off, 96, "%s", c->reading), then `j` TAIL. *)
Lemma p9_prov_site : forall n, H_TAIL n ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (v : pf_sv)
         (c t : Z) (s : list Z) (rc : rconf) (nm : list Z) (o : nat) (ln : Z) (d : list (list Z))
         (k : pf_prov) (gi : nat),
    pf_ctx m fc (bv_unsigned sp) lo v c t s o ln d n ->
    pf_state m (bv_unsigned sp) c (pf_prov_mid k rc gi) (Some gi) nm (length (skipn o s)) ->
    pf_regs s0 s1 s2 s3 s5 s10 s11 (t + Z.of_nat (pf_next s o)) (ln + 1) ->
    pf_curslot m (bv_unsigned sp) c (Some gi) ->
    a0 = Z_to_bv 64 (rseg_addr c gi + pf_prov_off k) ->
    a1 = Z_to_bv 64 96 ->
    a2 = Z_to_bv 64 PF_STR_S ->
    a3 = Z_to_bv 64 (c + RC_READING) ->
    evt rsegs
      (pf_fin v sp gp tp F m lo c
         (r_lines (pf_prov_fin k rc gi, Some gi, nm) (ln + 1) (lines (skipn (pf_next s o) s))))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PF_PC_CNAME) fc None m (seg_rom rsegs)).
Proof.
  intros n HT ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo v c t s rc nm o ln d k gi HCTX HST HREGS HCS -> -> -> ->.
  pose proof HCTX as (HENV & HTXT & HSPL & Ho & _ & _).
  pose proof HST as (HRC & Hcur & HNM & Hcnt).
  destruct (pfc_env_lo _ _ _ _ _ _ HENV) as (Lo0 & Lsp & Lhi & Hap & Lie & Lsp63).
  pose proof HENV as (Hc0 & Hc16 & _ & Hni & _).
  destruct (pfc_printf_at m fc (bv_unsigned sp) lo c v HENV) as (STP & HIE & HSP & HFRM & MI & TM & HG1 & (can & HG2)).
  pose proof HRC as (cbs & HCB & HCE). pose proof HCE as (HCL & HC32 & _).
  pose proof (bytes_at_bound _ _ _ _ HCB) as HCBB.
  unfold SEG_C_SIZE in HCL.
  destruct (pfc_upd_fields rc gi (fun g => pf_prov_set k (pf_prov_old k g) g)) as (EL & _ & _ & ERD & _).
  apply (proj1 (pfc_cur_ok_upd_iff rc gi _ (Some gi))) in Hcur. cbn [pf_cur_ok] in Hcur.
  unfold pf_prov_mid in HC32. rewrite EL in HC32.
  destruct (pfc_prov_off_range k) as [Hk1 Hk2].
  set (off := pf_prov_off k) in *.
  set (r := rc_reading rc).
  pose proof (pfc_reading_cstr m c _ HRC Hc16) as HRD. unfold pf_prov_mid in HRD. rewrite ERD in HRD. fold r in HRD.
  assert (Hrl : (length r < 96)%nat).
  { destruct HCE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & Hs & _) & _). unfold pf_prov_mid in Hs.
    rewrite ERD in Hs. exact Hs. }
  pose proof HRD as (rbs & rsl & RB & RZ & RN & RSL).
  assert (Hrb : Forall pfc_zbyte r) by (rewrite <- RZ; apply pfc_zs_byte).
  assert (Hspan : cstr_span (c + RC_READING) r <= 96).
  { unfold cstr_span, RC_READING. Z.div_mod_to_equations. lia. }
  assert (Hspan0 : 0 <= cstr_span (c + RC_READING) r).
  { unfold cstr_span. pose proof (Z.mod_pos_bound (- (c + RC_READING + Z.of_nat (length r) + 1)) 8). lia. }
  set (D := c + 356 * Z.of_nat gi + off).
  assert (ED : rseg_addr c gi + off = D) by (unfold rseg_addr, RSEG_SIZE, D; lia).
  rewrite ED.
  assert (HDr : 0 < D /\ D + 96 <= c + 11392) by (unfold D; lia).
  unfold apart, SEG_C_SIZE in Hap.
  unfold PF_PC_CNAME. zstep.
  eapply evt_cut.
  { eapply SNP with (lo := bv_unsigned sp - SNPRINTF_K) (fmt := [37; 115]) (ps := [Ps]) (args := [APtr r])
                    (T := r ++ []) (junk := fld (Z.to_nat (D - c)) 96 cbs) (canary := can);
      rewrite ?(unsigned_lit PF_STR_S), ?(unsigned_lit 96), ?(unsigned_lit D) by (unfold PF_STR_S; lia).
    - exact (pfc_fmt_s m MI).
    - unfold snprintf_c.RO_LO, PF_STR_S. lia.
    - unfold snprintf_c.RO_END, PF_STR_S. cbn [length]. lia.
    - reflexivity.
    - cbn [pf_args_ok]. split; [|exact I].
      apply pfc_arg_cstr; [exact HRD | unfold RC_READING; lia | unfold RC_READING, SNPRINTF_K in *; lia
                          | unfold RC_READING in *; lia].
    - reflexivity.
    - apply (pfc_dst_blk m c cbs D 96 HCB); [rewrite HCL; exact (pfc_c_wr m c _ HRC Hni) | lia | rewrite HCL; lia].
    - lia.
    - rewrite app_nil_r. lia.
    - lia.
    - unfold SNPRINTF_K in *. lia.
    - exact (pfc_noimg_sub c SEG_C_SIZE D 96 Hni ltac:(lia) ltac:(unfold SEG_C_SIZE; lia)).
    - exact STP.
    - lia.
    - exact HIE.
    - exact HSP.
    - exact HFRM.
    - exact MI.
    - exact TM.
    - exact HG1.
    - exact HG2. }
  intros ms' POST. unfold printf_post in POST.
  destruct POST as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & Ft & fc' & m' &
                    E & MU & WM & MI' & TM' & FRM & HF' & ST' & HB').
  subst ms'.
  rewrite ?(unsigned_lit 96), ?(unsigned_lit D) in MU, HB' by lia.
  rewrite app_nil_r, firstn_all2 in MU, HB' by lia.
  rewrite ret_pc_even by (try lia; reflexivity).
  (* 0x15b7c: j TAIL *)
  zstep.
  set (W := [(bv_unsigned sp - SNPRINTF_K, bv_unsigned sp); (D, D + Z.of_nat (length r) + 1)]) in *.
  assert (LOW : forall x, ~ outside W x -> lo <= x < bv_unsigned sp \/ c <= x < c + SEG_C_SIZE).
  { intros x Hx. unfold W in Hx. destruct (p9_not_out2 _ _ _ _ _ Hx); unfold SNPRINTF_K, SEG_C_SIZE in *; lia. }
  assert (HRC' : rconf_at rsegs m' c (pf_prov_fin k rc gi)).
  { exists (upd_bytes cbs (356 * gi + Z.to_nat off) (zb r ++ [ZERO])). split.
    - replace (356 * gi + Z.to_nat off)%nat with (Z.to_nat (D - c)) by (unfold D; lia).
      replace (zb r ++ [ZERO]) with (pf_bytes (r ++ [0])) by (unfold pf_bytes, zb; rewrite map_app; reflexivity).
      apply (pfc_bytes_patch W m m' c cbs D _ HCB MU HB'); [lia | unfold pf_bytes; rewrite length_map, length_app; cbn [length]; lia |].
      intros x Hx Hn. unfold pf_bytes in Hn. rewrite length_map, length_app in Hn. cbn [length] in Hn.
      unfold W. cbn [outside]. unfold SNPRINTF_K. repeat split; lia.
    - unfold pf_prov_fin. fold r. rewrite (pfc_snprintf_s_id 96 r RN ltac:(lia)).
      apply pfc_enc_prov_fin; [exact HCE | exact Hcur | exact Hrl | exact RN | exact Hrb]. }
  assert (FW : pfc_fw (bv_unsigned sp) lo c W) by (apply pfc_fw_low; exact LOW).
  assert (PR : forall x, pfc_scr (bv_unsigned sp) x -> ~ outside W x -> exists b, mrd rsegs m' (wa x) = Some b).
  { intros x Hx Hw. exfalso. unfold pfc_scr, PF_CURSLOT, PF_SAVE in Hx.
    destruct (LOW x Hw); unfold SEG_C_SIZE in *; lia. }
  assert (ST'' : stk rsegs m' lo (bv_unsigned sp)).
  { pose proof HENV as (_ & _ & _ & _ & _ & _ & (ST & _) & _).
    apply (pfc_stk_back W m m' lo (bv_unsigned sp) SNPRINTF_K); [ | exact MU | exact WM | exact ST'
                                                             | unfold SNPRINTF_K; lia | unfold SNPRINTF_K; lia |].
    - exact (proj1 (stk_split rsegs m lo (bv_unsigned sp) (bv_unsigned sp + PARSE_FILE_FRAME) ST
                               ltac:(unfold PARSE_FILE_FRAME; lia))).
    - intros x Hx. unfold W, SNPRINTF_K in *. cbn [outside]. repeat split; lia. }
  pose proof (pfc_ctx_call m m' fc fc' (bv_unsigned sp) lo v c t s o ln d n W HCTX MU WM FW PR ST'' MI' TM' FRM)
    as HCTX'.
  destruct (pfc_hctx_next m' fc' (bv_unsigned sp) lo v c t s o ln d n HCTX') as (HH & Hlt & Hn').
  assert (MU' : munch (pfc_W (bv_unsigned sp) c) m m').
  { apply (munch_weaken W _ m m'); [|exact MU]. intros x Hx. unfold pfc_W, RC_PARSE_W, PARSE_FILE_STACK,
      REFUSE_STACK, PRINTF_K, PARSE_FILE_FRAME, RC_N, W, SNPRINTF_K in *. cbn [outside] in *. repeat split; lia. }
  assert (HCS' : pf_curslot m' (bv_unsigned sp) c (Some gi)).
  { apply (pfc_curslot_call m m' fc (bv_unsigned sp) lo c v (Some gi) W HENV HCS MU).
    intros x Hx. unfold W, SNPRINTF_K, PF_CURSLOT in *. cbn [outside]. repeat split; lia. }
  eapply evt_mono.
  { eapply HT; [exact HH | | exact Hn' | exact HREGS | exact HCS'].
    split; [exact HRC'|]. split; [apply pfc_cur_ok_upd_iff; exact Hcur|].
    split.
    - apply (pfc_nm_call m m' fc (bv_unsigned sp) lo c v nm W HENV HNM MU).
      intros x Hx. unfold W, SNPRINTF_K, PF_NAMEBUF, PF_SAVE in *. cbn [outside]. repeat split; lia.
    - apply pfc_cnt_upd_iff. apply (pfc_cnt_mono rc (length (skipn o s))); [|lia].
      exact (proj1 (pfc_cnt_upd_iff rc gi _ _) Hcnt). }
  intros ms Hp. eapply pf_fin_weaken; [exact Hp | exact MU' | exact WM | exact HF'].
Qed.

Lemma p9_provm : forall n, H_TAIL n -> H_PROVM n.
Proof.
  intros n HT. unfold H_PROVM. intros until gi. intros HCTX HST HREGS HCS Ha0 Ha1 Ha2.
  pose proof HCTX as (_ & _ & HSPL & _).
  pose proof (pfc_ld_reading m (bv_unsigned sp) c HSPL) as HLD.
  unfold PF_PC_PROVM. zstep.
  eapply p9_prov_site; [exact HT | exact HCTX | exact HST | exact HREGS | exact HCS | exact Ha0 | exact Ha1
                       | exact Ha2 | reflexivity].
Qed.

Lemma p9_prov : forall n, H_TAIL n -> H_PROV n.
Proof.
  intros n HT. unfold H_PROV. intros until gi. intros HCTX HST HREGS HCS Ha0 Ha2.
  unfold PF_PC_PROV. zstep.
  eapply p9_provm; [exact HT | exact HCTX | exact HST | exact HREGS | exact HCS | exact Ha0 | reflexivity
                   | exact Ha2].
Qed.

(** CNAME (0x15b78): snprintf(cur_name, 16, "%s", name), then `j` TAIL with the new cur_name. *)
Lemma p9_cname : forall n, H_TAIL n -> H_CNAME n.
Proof.
  intros n HT. unfold H_CNAME.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo v c t s rc nm o ln d gi np name HCTX HST HREGS HCS -> -> -> -> HX HXB HXL.
  pose proof HCTX as (HENV & HTXT & HSPL & Ho & _ & _).
  pose proof HST as (HRC & Hcur & HNM & Hcnt).
  destruct (pfc_env_lo _ _ _ _ _ _ HENV) as (Lo0 & Lsp & Lhi & Hap & Lie & Lsp63).
  pose proof HENV as (Hc0 & Hc16 & _ & Hni & _ & _ & (ST & _) & _).
  pose proof (pfc_env_al _ _ _ _ _ _ HENV) as Hal.
  destruct (pfc_printf_at m fc (bv_unsigned sp) lo c v HENV) as (STP & HIE & HSP & HFRM & MI & TM & HG1 & (can & HG2)).
  pose proof HNM as (f & HBF & HFE). pose proof HFE as (HFL & _).
  pose proof HX as (xbs & xsl & XB & XZ & XN & XSL).
  assert (Hxb : Forall pfc_zbyte name) by (rewrite <- XZ; apply pfc_zs_byte).
  destruct HXB as [HXB1 HXB2].
  set (D := bv_unsigned sp + PF_NAMEBUF).
  assert (Hspan : np + cstr_span np name <= D).
  { unfold cstr_span, D, PF_NAMEBUF, PF_BUF in *. Z.div_mod_to_equations. lia. }
  assert (Hspan0 : 0 <= cstr_span np name).
  { unfold cstr_span. pose proof (Z.mod_pos_bound (- (np + Z.of_nat (length name) + 1)) 8). lia. }
  unfold apart, SEG_C_SIZE in Hap.
  unfold PF_PC_CNAME. zstep.
  eapply evt_cut.
  { eapply SNP with (lo := bv_unsigned sp - SNPRINTF_K) (fmt := [37; 115]) (ps := [Ps]) (args := [APtr name])
                    (T := name ++ []) (junk := f) (canary := can);
      rewrite ?(unsigned_lit PF_STR_S), ?(unsigned_lit 16), ?(unsigned_lit D), ?(unsigned_lit np)
        by (unfold D, PF_STR_S, PF_NAMEBUF, PF_BUF in *; lia).
    - exact (pfc_fmt_s m MI).
    - unfold snprintf_c.RO_LO, PF_STR_S. lia.
    - unfold snprintf_c.RO_END, PF_STR_S. cbn [length]. lia.
    - reflexivity.
    - cbn [pf_args_ok]. split; [|exact I].
      apply pfc_arg_cstr; [exact HX | unfold PF_BUF in *; lia | right; unfold PF_BUF in *; lia | left; exact Hspan].
    - reflexivity.
    - replace (Z.to_nat 16) with (length f) by (rewrite HFL; reflexivity).
      apply (pfc_rw_of_stk m lo (bv_unsigned sp + PARSE_FILE_FRAME) D f HBF ST); unfold D, PF_NAMEBUF, PARSE_FILE_FRAME;
        [lia | rewrite HFL; lia].
    - lia.
    - rewrite app_nil_r. lia.
    - unfold D, PF_NAMEBUF. lia.
    - right. unfold D, PF_NAMEBUF. lia.
    - apply pfc_img_free_hi. unfold D, PF_NAMEBUF. lia.
    - exact STP.
    - lia.
    - exact HIE.
    - exact HSP.
    - exact HFRM.
    - exact MI.
    - exact TM.
    - exact HG1.
    - exact HG2. }
  intros ms' POST. unfold printf_post in POST.
  destruct POST as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & Ft & fc' & m' &
                    E & MU & WM & MI' & TM' & FRM & HF' & ST' & HB').
  subst ms'.
  rewrite ?(unsigned_lit 16), ?(unsigned_lit D) in MU, HB' by (unfold D, PF_NAMEBUF in *; lia).
  rewrite app_nil_r, firstn_all2 in MU, HB' by lia.
  rewrite ret_pc_even by (try lia; reflexivity).
  (* 0x15b7c: j TAIL *)
  zstep.
  set (W := [(bv_unsigned sp - SNPRINTF_K, bv_unsigned sp); (D, D + Z.of_nat (length name) + 1)]) in *.
  assert (FW : pfc_fw (bv_unsigned sp) lo c W).
  { intros x Hx. unfold W in Hx. destruct (p9_not_out2 _ _ _ _ _ Hx) as [Q|Q].
    - left. unfold SNPRINTF_K in Q. lia.
    - right; right. unfold pfc_scr, PF_SAVE. right; right. unfold D, PF_NAMEBUF in Q. lia. }
  assert (PR : forall x, pfc_scr (bv_unsigned sp) x -> ~ outside W x -> exists b, mrd rsegs m' (wa x) = Some b).
  { intros x Hx Hw. apply (pfc_bytes_mrd m' D (pf_bytes (name ++ [0])) x HB').
    unfold pf_bytes. rewrite length_map, length_app. cbn [length].
    unfold W in Hw. destruct (p9_not_out2 _ _ _ _ _ Hw) as [Q|Q]; [|lia].
    exfalso. unfold pfc_scr, PF_CURSLOT, PF_SAVE, SNPRINTF_K in *. lia. }
  assert (ST'' : stk rsegs m' lo (bv_unsigned sp)).
  { apply (pfc_stk_back W m m' lo (bv_unsigned sp) SNPRINTF_K); [ | exact MU | exact WM | exact ST'
                                                             | unfold SNPRINTF_K; lia | unfold SNPRINTF_K; lia |].
    - exact (proj1 (stk_split rsegs m lo (bv_unsigned sp) (bv_unsigned sp + PARSE_FILE_FRAME) ST
                               ltac:(unfold PARSE_FILE_FRAME; lia))).
    - intros x Hx. unfold W, D, SNPRINTF_K, PF_NAMEBUF in *. cbn [outside]. repeat split; lia. }
  pose proof (pfc_ctx_call m m' fc fc' (bv_unsigned sp) lo v c t s o ln d n W HCTX MU WM FW PR ST'' MI' TM' FRM)
    as HCTX'.
  destruct (pfc_hctx_next m' fc' (bv_unsigned sp) lo v c t s o ln d n HCTX') as (HH & Hlt & Hn').
  assert (MU' : munch (pfc_W (bv_unsigned sp) c) m m').
  { apply (munch_weaken W _ m m'); [|exact MU]. intros x Hx. unfold pfc_W, RC_PARSE_W, PARSE_FILE_STACK,
      REFUSE_STACK, PRINTF_K, PARSE_FILE_FRAME, W, D, SNPRINTF_K, PF_NAMEBUF in *. cbn [outside] in *.
    repeat split; lia. }
  assert (HNM' : pf_nm_at m' D name).
  { exists (upd_bytes f 0 (zb name ++ [ZERO])). split.
    - replace (zb name ++ [ZERO]) with (pf_bytes (name ++ [0])) by (unfold pf_bytes, zb; rewrite map_app; reflexivity).
      replace 0%nat with (Z.to_nat (D - D)) by lia.
      apply (pfc_bytes_patch W m m' D f D _ HBF MU HB'); [lia | unfold pf_bytes; rewrite length_map, length_app, HFL; cbn [length]; lia |].
      intros x Hx Hn. unfold pf_bytes in Hn. rewrite length_map, length_app in Hn. cbn [length] in Hn.
      rewrite HFL in Hx. unfold W, SNPRINTF_K, D, PF_NAMEBUF in *. cbn [outside]. repeat split; lia.
    - apply pfc_cstr_enc_new; [exact HFL | lia | exact XN | exact Hxb]. }
  assert (HCS' : pf_curslot m' (bv_unsigned sp) c (Some gi)).
  { apply (pfc_curslot_call m m' fc (bv_unsigned sp) lo c v (Some gi) W HENV HCS MU).
    intros x Hx. unfold W, D, SNPRINTF_K, PF_CURSLOT, PF_NAMEBUF in *. cbn [outside]. repeat split; lia. }
  rewrite (pfc_snprintf_s_id 16 name XN ltac:(lia)).
  eapply evt_mono.
  { eapply HT; [exact HH | | exact Hn' | exact HREGS | exact HCS'].
    split; [|split; [exact Hcur | split; [exact HNM' | exact Hcnt]]].
    apply (pfc_rconf_munch W m m' c rc HRC MU). intros x Hx. unfold W, D, SNPRINTF_K, PF_NAMEBUF, SEG_C_SIZE in *.
    cbn [outside]. repeat split; lia. }
  intros ms Hp. eapply pf_fin_weaken; [exact Hp | exact MU' | exact WM | exact HF'].
Qed.

End P9U.

(** Piece P9 of reac_segconf_parse_file (UBSan): the shared sites. *)
Theorem pf_p9_holds : refuse_contract -> snprintf_contract -> S_P9.
Proof.
  intros REF SNP n.
  split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]]; intros HT.
  - exact (p9_outs REF n HT).
  - exact (p9_href REF n HT).
  - exact (p9_clr n HT).
  - exact (p9_knock REF n HT).
  - exact (p9_kref REF n HT).
  - exact (p9_nokey REF n HT).
  - exact (p9_prov SNP n HT).
  - exact (p9_provm SNP n HT).
  - exact (p9_cname SNP n HT).
Qed.
