From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells FP Arr.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib Require Import CJBridge.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib Require MemNorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YK1j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.Lib Require ITree.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.Spec Require Prelim.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.Reloc Require RStep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.G Require G_pad.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.GX Require Printf_model Printf_text G_printf_core_common.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.GX Require G_sn_write G_vsnprintf G_snprintf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.I Require InstFmtP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import printf_facts_c snprintf_c snprintf_stk_c.
Import ListNotations.
Open Scope Z_scope.

Module PI := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.GX.G_printf_core_common.G_printf_iface.

Definition tpc (p : pf_piece) : Printf_text.pf_piece :=
  match p with
  | PLit b => Printf_text.PLit b | Pd => Printf_text.Pd | Pc => Printf_text.Pc | Px04 => Printf_text.Px04
  | Px02 => Printf_text.Px02 | Pllu => Printf_text.Pllu | Ps => Printf_text.Ps | Pps => Printf_text.Pps
  end.

Definition ta (a : pf_arg) : Printf_text.pf_arg :=
  match a with AInt v => Printf_text.AInt v | AU64 u => Printf_text.AU64 u | APtr s => Printf_text.APtr s end.

Definition text_facts (fmt : list Z) (ps : list pf_piece) (args : list pf_arg) (T : list Z) : Prop :=
  Printf_model.printf_model (St:=list Z) (PI.OUT_snf (Prelim.zlength T)) PI.OUTFP_snf (fmt ++ [0])
      (Printf_text.pf_pargs (map tpc ps) (map ta args)) [] = ITree.Ret (ITree.Exc.Ok (Prelim.zlength T, T))
  /\ Printf_model.pass1_ok (fmt ++ [0]) = true
  /\ Forall (fun c => 0 <= c < 256) (fmt ++ [0]).

Lemma digits_eq : forall f x acc, Printf_text.pf_digits f x acc = pf_digits f x acc.
Proof.
  induction f as [|f IH]; intros x acc; cbn [Printf_text.pf_digits pf_digits]; [reflexivity|].
  destruct (x <? 10); [reflexivity | apply IH].
Qed.

Lemma hexs_eq : forall f x acc, Printf_text.pf_hexs f x acc = pf_hexs f x acc.
Proof.
  induction f as [|f IH]; intros x acc; cbn [Printf_text.pf_hexs pf_hexs]; [reflexivity|].
  unfold Printf_text.pf_hexd, pf_hexd. destruct (x <? 16); [reflexivity | apply IH].
Qed.

Lemma text_tr : forall ps args, Printf_text.pf_text (map tpc ps) (map ta args) = pf_text ps args.
Proof.
  induction ps as [|p ps IH]; intros args.
  - destruct args; reflexivity.
  - destruct p; cbn [map tpc Printf_text.pf_text pf_text].
    + rewrite IH. reflexivity.
    + destruct args as [|[v|u|s] a']; cbn [map ta]; try reflexivity.
      rewrite IH. unfold Printf_text.pf_dec, pf_dec. rewrite !digits_eq. reflexivity.
    + destruct args as [|[v|u|s] a']; cbn [map ta]; try reflexivity. rewrite IH. reflexivity.
    + destruct args as [|[v|u|s] a']; cbn [map ta]; try reflexivity.
      rewrite IH. unfold Printf_text.pf_hex4, pf_hex4. rewrite hexs_eq. reflexivity.
    + destruct args as [|[v|u|s] a']; cbn [map ta]; try reflexivity.
      rewrite IH. unfold Printf_text.pf_hex2, pf_hex2. rewrite hexs_eq. reflexivity.
    + destruct args as [|[v|u|s] a']; cbn [map ta]; try reflexivity.
      rewrite IH. unfold Printf_text.pf_udec, pf_udec. rewrite digits_eq. reflexivity.
    + destruct args as [|[v|u|s] a']; cbn [map ta]; try reflexivity. rewrite IH. reflexivity.
    + destruct args as [|[k|u|s] [|[v|u2|s2] a']]; cbn [map ta]; try reflexivity. rewrite IH. reflexivity.
Qed.

Lemma parse_tr_n : forall n f, (length f < n)%nat -> Printf_text.pf_parse f = option_map (map tpc) (pf_parse f).
Proof.
  induction n as [|n IH]; intros f Hf; [lia|].
  destruct f as [|b r]; [reflexivity|]. cbn [Printf_text.pf_parse pf_parse].
  repeat first
    [ match goal with |- context [Printf_text.pf_parse ?x] =>
        rewrite (IH x) by (cbn [length] in Hf |- *; lia) end
    | match goal with |- context [if ?c then _ else _] => destruct c end
    | match goal with |- context [match ?l with [] => _ | _ :: _ => _ end] => destruct l end ];
  try (match goal with |- context [pf_parse ?x] => destruct (pf_parse x) end); reflexivity.
Qed.

Lemma parse_tr : forall f ps, pf_parse f = Some ps -> Printf_text.pf_parse f = Some (map tpc ps).
Proof. intros f ps H. rewrite (parse_tr_n (S (length f)) f) by lia. rewrite H. reflexivity. Qed.

Lemma ta_int : forall args v, In (Printf_text.AInt v) (map ta args) -> In (AInt v) args.
Proof.
  intros args v H. apply in_map_iff in H. destruct H as ([w|u|s] & E & Hin); cbn in E; try discriminate E.
  injection E as ->. exact Hin.
Qed.

Lemma ta_u64 : forall args u, In (Printf_text.AU64 u) (map ta args) -> In (AU64 u) args.
Proof.
  intros args u H. apply in_map_iff in H. destruct H as ([w|v|s] & E & Hin); cbn in E; try discriminate E.
  injection E as ->. exact Hin.
Qed.

Lemma args_int : forall m S lo D n args rs, pf_args_ok m S lo D n rs args ->
  forall v, In (AInt v) args -> -2^31 <= v < 2^31.
Proof.
  induction args as [|a args IH]; intros rs H v Hv; [destruct Hv|].
  destruct rs as [|r rs]; [destruct H|]. destruct H as [H1 H2].
  destruct Hv as [E|Hv]; [subst a; cbn [pf_arg_ok] in H1; exact (proj1 H1) | exact (IH rs H2 v Hv)].
Qed.

Lemma args_u64 : forall m S lo D n args rs, pf_args_ok m S lo D n rs args ->
  forall u, In (AU64 u) args -> 0 <= u.
Proof.
  induction args as [|a args IH]; intros rs H u Hu; [destruct Hu|].
  destruct rs as [|r rs]; [destruct H|]. destruct H as [H1 H2].
  destruct Hu as [E|Hu]; [|exact (IH rs H2 u Hu)].
  subst a. cbn [pf_arg_ok] in H1. rewrite <- H1. pose proof (bv_unsigned_in_range _ r). lia.
Qed.

Lemma text_ok : forall m S lo D n rs fmt ps args T,
  pf_args_ok m S lo D n rs args -> pf_parse fmt = Some ps -> pf_text ps args = Some T ->
  Z.of_nat (length T) < 2^31 - 1 -> text_facts fmt ps args T.
Proof.
  intros m S lo D n rs fmt ps args T PA Hp Ht HT.
  destruct (Printf_text.printf_text_ok fmt (map tpc ps) (map ta args) T (parse_tr fmt ps Hp)
              ltac:(rewrite text_tr; exact Ht)
              (fun v Hv => args_int _ _ _ _ _ _ _ PA v (ta_int args v Hv))
              (fun u Hu => args_u64 _ _ _ _ _ _ _ PA u (ta_u64 args u Hu))
              ltac:(unfold Prelim.zlength; lia) ltac:(left; unfold Prelim.zlength; lia))
    as (M & P & _ & B).
  split; [exact M | split; [exact P | exact B]].
Qed.

Lemma str_ok : forall m S lo D n dn r s,
  pf_arg_ok m S lo D n r (APtr s) -> lo + 232 <= S -> Z.of_nat dn <= n ->
  @PI.arg_ok InstFmtP.N_img_fmt lo lo 0 lo 0 D (Z.of_nat dn) m lo S lo r (Printf_model.PA_s s).
Proof.
  intros m S lo D n dn r s [HF [slack (BY & PAD & POS & L1 & L2)]] HS Hd.
  exists slack. unfold Prelim.zlength.
  split; [unfold pf_bytes in BY; rewrite map_app, <- app_assoc in BY; exact BY|].
  split; [exact HF|]. split; [exact PAD|]. split; [exact POS|].
  repeat split; lia.
Qed.

Lemma pargs_ok : forall m S lo D n dn ps args rs,
  pf_args_ok m S lo D n rs args -> lo + 232 <= S -> Z.of_nat dn <= n ->
  @PI.args_ok InstFmtP.N_img_fmt lo lo 0 lo 0 D (Z.of_nat dn) m lo S lo rs
    (Printf_text.pf_pargs (map tpc ps) (map ta args)).
Proof.
  intros m S lo D n dn ps. induction ps as [|p ps IH]; intros args rs H HS Hd; [destruct rs; exact I|].
  destruct p; cbn [map tpc Printf_text.pf_pargs].
  - apply IH; assumption.
  - destruct args as [|[v|u|s] a']; cbn [map ta]; try (destruct rs; exact I).
    destruct rs as [|r rs]; [destruct H|]. destruct H as [H1 H2].
    split; [exact H1 | apply IH; assumption].
  - destruct args as [|[v|u|s] a']; cbn [map ta]; try (destruct rs; exact I).
    destruct rs as [|r rs]; [destruct H|]. destruct H as [H1 H2].
    split; [exact H1 | apply IH; assumption].
  - destruct args as [|[v|u|s] a']; cbn [map ta]; try (destruct rs; exact I).
    destruct rs as [|r rs]; [destruct H|]. destruct H as [H1 H2].
    split; [split; [apply Z.mod_pos_bound; lia | exact (proj2 H1)] | apply IH; assumption].
  - destruct args as [|[v|u|s] a']; cbn [map ta]; try (destruct rs; exact I).
    destruct rs as [|r rs]; [destruct H|]. destruct H as [H1 H2].
    split; [split; [apply Z.mod_pos_bound; lia | exact (proj2 H1)] | apply IH; assumption].
  - destruct args as [|[v|u|s] a']; cbn [map ta]; try (destruct rs; exact I).
    destruct rs as [|r rs]; [destruct H|]. destruct H as [H1 H2].
    split; [exact H1 | apply IH; assumption].
  - destruct args as [|[v|u|s] a']; cbn [map ta]; try (destruct rs; exact I).
    destruct rs as [|r rs]; [destruct H|]. destruct H as [H1 H2].
    split; [exact (str_ok m S lo D n dn r s H1 HS Hd) | apply IH; assumption].
  - destruct args as [|[k|u|s] [|[v|u2|s2] a']]; cbn [map ta]; try (destruct rs; exact I).
    destruct rs as [|r1 [|r2 rs]]; [destruct H | destruct H as [_ []] |]. destruct H as [H1 [H2 H3]].
    split; [exact H1|]. split; [exact (str_ok m S lo D n dn r2 s2 H2 HS Hd) | apply IH; assumption].
Qed.

Definition ivs (l : list (word * word)) : list (Z * Z) :=
  map (fun s => (bv_unsigned (fst s), bv_unsigned (fst s) + bv_unsigned (snd s))) l.

Fixpoint cov (L : list (Z * Z)) (cur : Z) : Z :=
  match L with [] => cur | (a, b) :: L' => cov L' (if a <=? cur then Z.max cur b else cur) end.

Lemma cov_in : forall L cur x, cur <= x < cov L cur -> exists a b, In (a, b) L /\ a <= x < b.
Proof.
  induction L as [|[a b] L IH]; intros cur x Hx; cbn [cov] in Hx; [lia|].
  revert Hx. destruct (a <=? cur) eqn:E; intros Hx.
  - apply Z.leb_le in E. destruct (Z.lt_ge_cases x (Z.max cur b)) as [H|H].
    + exists a, b. split; [left; reflexivity | lia].
    + destruct (IH (Z.max cur b) x ltac:(lia)) as (a' & b' & Hin & Hab). exists a', b'.
      split; [right; exact Hin | exact Hab].
  - destruct (IH cur x Hx) as (a' & b' & Hin & Hab). exists a', b'. split; [right; exact Hin | exact Hab].
Qed.

Definition IMG_PAGES : Z := Eval vm_compute in cov (ivs (segments_reserved rsegs)) 0x10000.

Lemma rsegs_pages : cov (ivs (segments_reserved rsegs)) 0x10000 = IMG_PAGES.
Proof. vm_compute. reflexivity. Qed.

Lemma img_free_bound : forall D n, 0 <= D -> 0 < n -> pf_img_free D n -> D + n <= 0x10000 \/ IMG_PAGES <= D.
Proof.
  intros D n HD Hn F.
  assert (C : forall x, 0x10000 <= x < IMG_PAGES -> exists s, In s (segments_reserved rsegs)
                /\ bv_unsigned (fst s) <= x < bv_unsigned (fst s) + bv_unsigned (snd s)).
  { intros x Hx. rewrite <- rsegs_pages in Hx. destruct (cov_in _ _ _ Hx) as (a & b & Hin & Hab).
    unfold ivs in Hin. apply in_map_iff in Hin. destruct Hin as (s & Es & Hs). injection Es as Ea Eb.
    exists s. split; [exact Hs | lia]. }
  assert (PL : 0x10000 < IMG_PAGES) by (vm_compute; reflexivity).
  destruct (Z.lt_ge_cases D 0x10000) as [H1|H1].
  - destruct (Z.le_gt_cases (D + n) 0x10000) as [H2|H2]; [left; exact H2|].
    destruct (C 0x10000 ltac:(lia)) as (s & Hs & Hx). exfalso.
    apply (F (0x10000 - D) ltac:(lia) s Hs). replace (D + (0x10000 - D)) with 0x10000 by lia. exact Hx.
  - destruct (Z.lt_ge_cases D IMG_PAGES) as [H2|H2]; [|right; exact H2].
    destruct (C D ltac:(lia)) as (s & Hs & Hx). exfalso.
    apply (F 0 ltac:(lia) s Hs). rewrite Z.add_0_r. exact Hx.
Qed.

Lemma seg_task : forall x, find_segment rsegs x 1 <> None -> x < TASK_SIZE.
Proof.
  intros x H. destruct (find_segment rsegs x 1) as [s|] eqn:E; [|congruence].
  pose proof (YK1j.find_segment_range _ _ _ _ E) as R. pose proof (YK1j.find_segment_in _ _ _ _ E) as I.
  assert (B : forallb (fun s => Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? IMG_PAGES) rsegs = true)
    by (vm_compute; reflexivity).
  assert (PT : IMG_PAGES <= TASK_SIZE) by (apply Z.leb_le; vm_compute; reflexivity).
  rewrite forallb_forall in B. specialize (B s I). apply Z.leb_le in B. lia.
Qed.

Lemma ro_range : forall a k, forallb (fun i => negb (ro_addr rsegs (wa (a + Z.of_nat i)))) (seq 0 k) = true ->
  forall i, 0 <= i < Z.of_nat k -> ro_addr rsegs (wa (a + i)) = false.
Proof.
  intros a k H i Hi. rewrite forallb_forall in H. specialize (H (Z.to_nat i) ltac:(apply in_seq; lia)).
  rewrite Z2Nat.id in H by lia. apply negb_true_iff in H. exact H.
Qed.

Lemma wview_of_mrd : forall m x b, mrd rsegs m x = Some b -> ro_addr rsegs x = false -> wview rsegs m x <> None.
Proof.
  intros m x b H R. unfold mrd in H. unfold wview. destruct (m x) as [b'|]; [discriminate|].
  unfold seg_rom, memory_read in H. unfold ro_addr in R. change (Z.of_N 1) with 1 in H.
  destruct (find_segment rsegs (bv_unsigned x) 1) as [sg|]; [|discriminate H].
  apply negb_false_iff in R. rewrite R.
  destruct (seg_readable sg); [|discriminate H]. change (N.to_nat 1) with 1%nat in H. cbn [segment_read_bytes] in H.
  destruct (segment_byte_at (seg_bytes sg) (Z.to_N (bv_unsigned x - Z.of_N (seg_base sg)))); [discriminate|].
  discriminate H.
Qed.

Lemma wr_of_bytes : forall m a bs, bytes_at rsegs m a bs ->
  (forall i, 0 <= i < Z.of_nat (length bs) -> ro_addr rsegs (wa (a + i)) = false) ->
  wr_at rsegs m a (Z.of_nat (length bs)).
Proof.
  intros m a bs (H0 & H1 & H) R. split; [exact H0|]. split; [exact H1|]. intros i Hi.
  destruct (nth_error bs (Z.to_nat i)) as [b|] eqn:E.
  - apply (wview_of_mrd m _ b); [|apply R; exact Hi].
    specialize (H (Z.to_nat i) ltac:(lia)). rewrite Z2Nat.id in H by lia. rewrite H. exact E.
  - apply nth_error_None in E. lia.
Qed.

Lemma rw8_of_bytes : forall m a v, bytes_at rsegs m a (le8 v) ->
  forallb (fun i => negb (ro_addr rsegs (wa (a + Z.of_nat i)))) (seq 0 8) = true ->
  CJ.Lib.Step.rw_cells rsegs m a [CJ.Lib.Cells.C8 v].
Proof.
  intros m a v B R. apply (proj2 (rw_cells_iff rsegs m a [C8 v])).
  split; [split; [cbn; tauto | cbn [cells_bytes cbytes]; rewrite app_nil_r; exact B]|].
  cbn [cells_size csize Nat.add]. rewrite <- (length_le8 v). apply wr_of_bytes; [exact B|].
  intros i Hi. rewrite length_le8 in Hi. exact (ro_range a 8 R i Hi).
Qed.

Lemma c_got : @G_pad.got_ssp InstFmtP.N_img_fmt = GOT_GUARD.
Proof. vm_compute. reflexivity. Qed.
Lemma c_guard : @G_pad.ssp_guard InstFmtP.N_img_fmt = GUARD.
Proof. vm_compute. reflexivity. Qed.
Lemma c_snprintf : @RStep.sym InstFmtP.N_img_fmt 0x7f000100 = SNPRINTF.
Proof. vm_compute. reflexivity. Qed.
Lemma c_gtop : @PI.GLOBALS_TOP InstFmtP.N_img_fmt = IMG_END.
Proof. vm_compute. reflexivity. Qed.

Lemma c_pages : IMG_END <= IMG_PAGES.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.

Lemma ssp_of_bytes : forall m canary,
  bytes_at rsegs m GOT_GUARD (le8 (Z_to_bv 64 GUARD)) -> bytes_at rsegs m GUARD (le8 canary) ->
  @G_pad.ssp_cells InstFmtP.N_img_fmt m canary.
Proof.
  intros m canary G Q. unfold G_pad.ssp_cells. rewrite c_got, c_guard.
  split; apply rw8_of_bytes; first [exact G | exact Q | vm_compute; reflexivity].
Qed.

Lemma task_bound : forall m D n junk, mem_inv rsegs m -> MemNorm.task_mem rsegs m ->
  rw_cells rsegs m D [CB n junk] -> (0 < n)%nat -> D + Z.of_nat n <= TASK_SIZE.
Proof.
  intros m D n junk MI TM [[W B] _] Hn. cbn [cells_wf cell_wf] in W. destruct W as [W _].
  cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. rewrite <- W.
  apply (CJ.Lib.Mem.bytes_at_task rsegs m D junk (mem_inv_to_cj rsegs m MI TM) seg_task B).
  destruct junk; cbn in W; [lia | discriminate].
Qed.

Lemma post_of_cj : forall ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo D n (dn : nat) T m canary ms',
  1 <= n -> Z.of_nat dn = Z.min (Z.of_nat (length T)) (n - 1) + 1 ->
  @G_vsnprintf.vsnprintf_x_post InstFmtP.N_img_fmt ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F D dn
    (map (Z_to_bv 8) (firstn (Z.to_nat (n - 1)) T) ++ [Z_to_bv 8 0]) (Prelim.zlength T) lo canary m ms' ->
  printf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo D (Z.of_nat (length T))
    (firstn (Z.to_nat (n - 1)) T) m ms'.
Proof.
  intros until ms'. intros Hn Hdn P. unfold G_vsnprintf.vsnprintf_x_post in P.
  destruct P as (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & Ft & fc' & m'
                 & Hms & MU & WM & MI & FRM & FOK & ST & _ & DST).
  destruct (mem_inv_of_cj rsegs m' MI) as [MI2 TM2].
  unfold printf_post. exists t0, t1, t2, a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, Ft, fc', m'.
  split; [exact Hms|].
  split; [replace (D + Z.of_nat (length (firstn (Z.to_nat (n - 1)) T)) + 1) with (D + Z.of_nat dn)
            by (rewrite length_firstn; lia); exact MU|].
  split; [exact WM|]. split; [exact MI2|]. split; [exact TM2|]. split; [exact FRM|]. split; [exact FOK|].
  split; [exact ST|].
  destruct DST as [[_ B] _]. cbn [CJ.Lib.Cells.cells_bytes CJ.Lib.Cells.cbytes] in B. rewrite app_nil_r in B.
  unfold pf_bytes. rewrite map_app. exact B.
Qed.

Theorem snprintf_stk_holds : snprintf_stk_contract.
Proof.
  unfold snprintf_stk_contract.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo canary
         fmt ps args T junk xs.
  cbv zeta.
  intros BYF RLO REND PARSE PAOK BYX XHI DXS TEXT DST Hn HT D0 DLO IMGF ST LO IMGLO SHI FRM MI TM GG GQ.
  destruct (text_ok _ _ _ _ _ _ fmt ps args T PAOK PARSE TEXT HT) as (MODEL & P1 & HF).
  assert (Edn : exists dn : nat, Z.of_nat dn = Z.min (Z.of_nat (length T)) (bv_unsigned a1 - 1) + 1)
    by (exists (Z.to_nat (Z.min (Z.of_nat (length T)) (bv_unsigned a1 - 1) + 1)); lia).
  destruct Edn as [dn Hdn].
  pose proof (task_bound m (bv_unsigned a0) _ junk MI TM DST ltac:(lia)) as DT.
  pose proof (img_free_bound (bv_unsigned a0) (bv_unsigned a1) ltac:(lia) ltac:(lia) IMGF) as IF.
  pose proof (proj2 (rw_cells_iff rsegs m (bv_unsigned a0) [CB (Z.to_nat (bv_unsigned a1)) junk]) DST) as DST1.
  cbn [map cell_to] in DST1.
  replace (Z.to_nat (bv_unsigned a1)) with (dn + (Z.to_nat (bv_unsigned a1) - dn))%nat in DST1 by lia.
  destruct (G_sn_write.rw_CB_split _ _ _ _ _ _ DST1) as [DSTd _].
  unfold SNPRINTF_K, RO_LO, RO_END in *.
  pose proof (pargs_ok m (bv_unsigned sp) lo (bv_unsigned a0) (bv_unsigned a1) dn ps args _ PAOK ltac:(lia) ltac:(lia))
    as AOK.
  pose proof (ssp_of_bytes m canary GG GQ) as SSP.
  pose proof (mem_inv_to_cj rsegs m MI TM) as MIc.
  pose proof InstFmtP.N_snprintf as RS. unfold G_snprintf.snprintf_x_stmt in RS.
  specialize (RS ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
                 (bv_unsigned a0) (bv_unsigned a1) (bv_unsigned a2) dn (firstn dn junk) (fmt ++ [0]) xs
                 (Printf_text.pf_pargs (map tpc ps) (map ta args)) lo canary (Prelim.zlength T) T).
  cbv zeta in RS. rewrite c_snprintf, c_gtop in RS. unfold PI.STATIC_SPLIT, G_snprintf.SNPRINTF_DEPTH in RS.
  pose proof c_pages as PG. unfold IMG_END, IMG_PAGES, TASK_SIZE in *.
  specialize (RS (eq_sym (Z_to_bv_bv_unsigned a0)) (eq_sym (Z_to_bv_bv_unsigned a1)) (eq_sym (Z_to_bv_bv_unsigned a2))
                 DSTd Hdn BYF HF P1 BYX ltac:(unfold Prelim.zlength; lia) AOK MODEL Hn ST ltac:(lia) ltac:(lia) SHI SSP MIc FRM
                 ltac:(unfold Prelim.zlength; rewrite length_app; cbn [length]; lia) RLO D0
                 ltac:(lia) ltac:(unfold Prelim.zlength; lia) ltac:(lia)).
  eapply evt_bridge; [| exact RS].
  intros ms' P. exact (post_of_cj ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo (bv_unsigned a0) (bv_unsigned a1) dn
                         T m canary ms' (proj1 Hn) Hdn P).
Qed.

Theorem snprintf_holds : snprintf_contract.
Proof.
  unfold snprintf_contract.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo canary
         fmt ps args T junk.
  cbv zeta.
  intros BYF RLO REND PARSE PAOK TEXT DST Hn HT D0 DLO IMGF ST LO IMGLO SHI FRM MI TM GG GQ.
  pose proof (proj1 ST) as Hlo. unfold SNPRINTF_K in LO.
  exact (snprintf_stk_holds ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
           F fc m lo canary fmt ps args T junk [] BYF RLO REND PARSE PAOK (bytes_at_nil rsegs m (bv_unsigned sp) ltac:(lia))
           ltac:(cbn [length]; lia)
           ltac:(cbn [length]; lia) TEXT DST Hn HT D0 DLO IMGF ST ltac:(unfold SNPRINTF_K; lia) IMGLO SHI FRM MI TM GG GQ).
Qed.
