(** reac-pw/fuzz_segconf, UBSan build: refuse's two printf callee premises (U/Prog/refuse_pf_c.v: rf_snprintf for
    the address prefix, rf_vsnprintf for the 17 refusal formats through refuse's va_list) follow from the printf
    contracts snprintf_contract (U/Prog/snprintf_c.v) and vsnprintf_contract (U/Prog/vsnprintf_c.v). The proof is the
    plain build's (Prog/refuse_pf.v, which explains it) over this build's image, contracts and seg_env (SA =
    SEG_UBSAN: GOT_GUARD 0x221b0, GUARD 0x53820, RO_END 0x1229c, IMG_END 0x54088 are its sa_got_guard, sa_guard,
    sa_ro_end, sa_img_end); the image-free lemmas come from the plain file's module RpfPure. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame FP Arr.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U Require MemNorm.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.Spec Require Prelim FmtFp.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.GX Require Printf_model.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require SegPrintfBridge.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require refuse_pf.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require Import seg_env.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require Import printf_facts_c snprintf_c printf_model_c
  vsnprintf_c refuse_pf_c.
Import OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog.refuse_pf.RpfPure.
Import ListNotations.
Open Scope Z_scope.

(** * This build's facts *)

(** The pf_arg snprintf reads for a spine argument. *)
Definition to_pf (x : arg) : pf_arg := match x with AS s => APtr s | AI z => AInt z end.

Lemma pf_digits_dec_go : forall f n acc, 0 <= n -> pf_digits f n acc = dec_go f n acc.
Proof.
  induction f as [|f IH]; intros n acc Hn; [reflexivity|]. rewrite rp_dec_go_S. cbn [pf_digits].
  destruct (Z.ltb_spec n 10) as [H|H].
  - rewrite Z.mod_small by lia. reflexivity.
  - apply IH. apply Z.div_pos; lia.
Qed.

Lemma dec_pf_dec : forall z, 0 <= z < 2 ^ 31 -> dec z = pf_dec z.
Proof.
  intros z Hz. rewrite rp_dec_nonneg by exact Hz. unfold pf_dec.
  replace (z <? 0) with false by (symmetry; apply Z.ltb_ge; lia). symmetry. apply pf_digits_dec_go. lia.
Qed.

Lemma pf_bytes_zs : forall bs, pf_bytes (zs bs ++ [0]) = bs ++ [ZERO].
Proof.
  intros bs. unfold pf_bytes. rewrite map_app. change (map (Z_to_bv 8) (zs bs)) with (zb (zs bs)).
  rewrite rp_zb_zs. reflexivity.
Qed.

(** The format at fp: its bytes and NUL. *)
Lemma fmt_bytes : forall m fp f, cstrz_at rsegs m fp f -> bytes_at rsegs m fp (pf_bytes (f ++ [0])).
Proof. intros m fp f (bs & B & <- & _). rewrite pf_bytes_zs. exact B. Qed.

(** A string argument as snprintf reads it: its bytes, its NUL and the slack up to the next 8-byte boundary, apart
    from the stack region [lo, S) and from the destination [D, D + n) inside the slot. *)
Lemma str_ok : forall m S lo Dslot D n r s, Dslot <= D -> D + n <= Dslot + RC_REFUSAL_LEN ->
  va_arg_ok rsegs m [(lo, S); (Dslot, Dslot + RC_REFUSAL_LEN)] r (AS s) -> pf_arg_ok m S lo D n r (APtr s).
Proof.
  intros m S lo Dslot D n r s HD1 HD2 (Hr0 & (bs & sl & B & <- & NZ & SL) & _ & AP).
  pose proof (Forall_inv AP) as AP1. pose proof (Forall_inv (Forall_inv_tail AP)) as AP2.
  cbn [fst snd] in AP1, AP2. unfold apart in AP1, AP2. unfold RC_REFUSAL_LEN in *.
  destruct (bv_unsigned_in_range 64 r) as [R0 _].
  unfold pf_arg_ok.
  set (k := (- (bv_unsigned r + Z.of_nat (length (zs bs)) + 1)) mod 8) in *.
  assert (K8 : 0 <= k < 8) by (apply Z.mod_pos_bound; lia).
  split; [apply rp_zs_pos; exact NZ|].
  exists (firstn (Z.to_nat k) sl).
  assert (LF : Z.of_nat (length (firstn (Z.to_nat k) sl)) = k) by (rewrite length_firstn; lia).
  split; [|split; [lia | split; [lia | split; lia]]].
  rewrite pf_bytes_zs.
  rewrite <- (firstn_skipn (Z.to_nat k) sl) in B.
  replace (bs ++ ZERO :: firstn (Z.to_nat k) sl ++ skipn (Z.to_nat k) sl)
    with ((bs ++ ZERO :: firstn (Z.to_nat k) sl) ++ skipn (Z.to_nat k) sl) in B
    by (rewrite <- app_assoc; reflexivity).
  apply bytes_at_app in B. destruct B as [B _].
  replace ((bs ++ [ZERO]) ++ firstn (Z.to_nat k) sl) with (bs ++ ZERO :: firstn (Z.to_nat k) sl)
    by (rewrite <- app_assoc; reflexivity).
  exact B.
Qed.

Lemma va_small : forall m W rs args, va_args_ok rsegs m W rs args -> Forall arg_small args.
Proof.
  intros m W rs args. revert rs. induction args as [|x args IH]; intros rs Hv; [constructor|].
  destruct rs as [|r rs]; [destruct Hv|]. destruct Hv as [Hx Hv]. constructor; [|exact (IH rs Hv)].
  destruct x as [s|z]; cbn [arg_small].
  - destruct Hx as (_ & (bs & sl & _ & _ & NZ & _) & Hl & _). split; [|exact NZ].
    apply Nat2Z.inj_le in Hl. change (Z.of_nat 65535%nat) with 65535 in Hl. exact Hl.
  - destruct Hx as [Hz _]. exact Hz.
Qed.

(** snprintf's arguments (rf_snprintf: a3 .. a7). *)
Lemma va_pf_args : forall m S lo Dslot D n rs args, Dslot <= D -> D + n <= Dslot + RC_REFUSAL_LEN ->
  va_args_ok rsegs m [(lo, S); (Dslot, Dslot + RC_REFUSAL_LEN)] rs args -> pf_args_ok m S lo D n rs (map to_pf args).
Proof.
  intros m S lo Dslot D n rs args HD1 HD2. revert rs.
  induction args as [|x args IH]; intros rs Hv; [destruct rs; exact I|].
  destruct rs as [|r rs]; [destruct Hv|]. destruct Hv as [Hx Hv]. split; [|exact (IH rs Hv)].
  destruct x as [s|z].
  - exact (str_ok m S lo Dslot D n r s HD1 HD2 Hx).
  - destruct Hx as [Hz Hr]. cbn [to_pf pf_arg_ok]. split; [lia|]. rewrite Hr. reflexivity.
Qed.

(** vsnprintf's arguments (rf_vsnprintf: the saved slots), read as sp_pargs gives them. *)
Lemma va_pm_args : forall m S lo Dslot D n args ps rs, Dslot <= D -> D + n <= Dslot + RC_REFUSAL_LEN ->
  Forall2 pa_rel args ps -> va_args_ok rsegs m [(lo, S); (Dslot, Dslot + RC_REFUSAL_LEN)] rs args ->
  pm_args_ok m S lo D n rs ps.
Proof.
  intros m S lo Dslot D n args ps rs HD1 HD2 HR. revert rs.
  induction HR as [|x p args ps Hxp HR IH]; intros rs Hv; [destruct rs; exact I|].
  destruct rs as [|r rs]; [destruct Hv|]. destruct Hv as [Hx Hv]. split; [|exact (IH rs Hv)].
  destruct x as [s|z]; cbn [pa_rel] in Hxp.
  - subst p. cbn [pm_arg_ok].
    pose proof Hx as (_ & (bs & sl & _ & _ & NZ & _) & _). rewrite (cut_nul_id s NZ).
    exact (str_ok m S lo Dslot D n r s HD1 HD2 Hx).
  - destruct Hx as [Hz Hr]. destruct Hxp as [ -> | [ -> | -> ] ]; cbn [pm_arg_ok pf_arg_ok].
    + split; [lia|]. rewrite Hr. reflexivity.
    + split; [lia|]. rewrite Hr. apply Z.mod_small. lia.
    + exact Hr.
Qed.

(** The text of the two address prefixes: pf_parse and pf_text compute SegModel.fmt. *)
Lemma text_ok : forall f a, In f [F_addr_line; F_addr] -> conv_kinds f = map arg_is_s a -> Forall arg_small a ->
  exists ps, pf_parse f = Some ps /\ pf_text ps (map to_pf a) = Some (fmt f a).
Proof.
  intros f a Hin Hk Ha. destruct Hin as [<-|[<-|[]]].
  - assert (K : conv_kinds F_addr_line = [true; false]) by (vm_compute; reflexivity).
    rewrite K in Hk. destruct a as [|[s|z1] [|[s2|z] [|x3 a]]]; cbn in Hk; try discriminate Hk.
    pose proof (Forall_inv Ha) as [_ Hs]. pose proof (Forall_inv (Forall_inv_tail Ha)) as Hz. cbn in Hz.
    exists [Ps; PLit 58; Pd; PLit 58; PLit 32]. split; [vm_compute; reflexivity|].
    rewrite fmt_addr_line, (cut_nul_id s Hs), (dec_pf_dec z Hz). reflexivity.
  - assert (K : conv_kinds F_addr = [true]) by (vm_compute; reflexivity).
    rewrite K in Hk. destruct a as [|[s|z1] [|x2 a]]; cbn in Hk; try discriminate Hk.
    pose proof (Forall_inv Ha) as [_ Hs].
    exists [Ps; PLit 58; PLit 32]. split; [vm_compute; reflexivity|].
    rewrite fmt_addr, (cut_nul_id s Hs). reflexivity.
Qed.

(** The destination: present and writable, one block of junk. *)
Lemma dst_cells : forall m D n junk, wr_at rsegs m D n -> bytes_at rsegs m D junk -> Z.of_nat (length junk) = n ->
  rw_cells rsegs m D [CB (Z.to_nat n) junk].
Proof.
  intros m D n junk W B L. subst n. rewrite Nat2Z.id. apply rw_cells_of_u8arr. split; assumption.
Qed.

Lemma saved_u64s : forall m a ws, saved_at rsegs m a ws -> bytes_at rsegs m a (u64s ws).
Proof. intros m a ws H. unfold saved_at in H. rewrite rp_u64s. exact H. Qed.

(** printf's post is refuse's: the same conjuncts, the text snprintf_s n f args and its NUL. *)
Lemma post_conv : forall ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m lo D n f args ms',
  printf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo D (snprintf_r f args) (snprintf_s n f args) m
    ms' ->
  rf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m lo D n f args ms'.
Proof.
  intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m lo D n f args ms' P.
  unfold printf_post in P.
  destruct P as (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & Ft & fc' & m'
                 & E & MU & WM & MI & TM & FR & FK & ST & BY).
  unfold rf_post, ret_post_fp.
  exists t0, t1, t2, a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, Ft, fc', m'.
  split; [exact E|]. split; [exact FR|]. split; [exact FK|]. split; [exact MU|]. split; [exact WM|].
  split; [exact MI|]. split; [exact TM|]. split; [exact ST|].
  unfold pf_bytes in BY. rewrite map_app in BY. exact BY.
Qed.

(** * The two premises *)
Theorem rf_snprintf_of : snprintf_contract -> rf_snprintf.
Proof.
  intros C. unfold rf_snprintf.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo Dslot
    f args FM DS ENV STK MI.
  destruct FM as (Hin & Hk & Hz & Hlo & Hhi & Hva).
  destruct DS as (D0 & Hn1 & HD1 & HD2 & NI & WR & (junk & BJ & LJ) & AP).
  destruct ENV as (FR & TM & (GG & g & GD) & IE & SH).
  destruct STK as (ST & SK & _ & _).
  pose proof (va_small _ _ _ _ Hva) as Hsm.
  destruct (text_ok f args Hin Hk Hsm) as (ps & HP & HT).
  pose proof (rp_fmt_bound _ f args rp_addr_small Hin Hk Hsm) as HB.
  assert (HN : 1 <= bv_unsigned a1 < 2 ^ 31) by (unfold RC_REFUSAL_LEN in HD2; lia).
  assert (HL : Z.of_nat (length (fmt f args)) < 2 ^ 31 - 1) by lia.
  assert (HK : lo <= bv_unsigned sp - SNPRINTF_K) by (unfold SNPRINTF_K; unfold PRINTF_K in SK; lia).
  pose proof (C ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
                lo g f ps (map to_pf args) (fmt f args) junk) as CC.
  cbv zeta in CC.
  eapply evt_mono.
  - exact (CC (fmt_bytes _ _ _ Hz) Hlo Hhi HP (va_pf_args _ _ _ _ _ _ _ _ HD1 HD2 Hva) HT
              (dst_cells _ _ _ _ WR BJ LJ) HN HL D0 AP NI ST HK IE SH FR MI TM GG GD).
  - intros ms' P. apply post_conv. exact P.
Qed.

Theorem rf_vsnprintf_of : vsnprintf_contract -> rf_vsnprintf.
Proof.
  intros C. unfold rf_vsnprintf.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo Dslot
    f slots args FM SV HVA HVB DS ENV STK MI.
  destruct FM as (Hin & Hk & Hz & Hlo & Hhi & Hva).
  destruct DS as (D0 & Hn1 & HD1 & HD2 & NI & WR & (junk & BJ & LJ) & AP).
  destruct ENV as (FR & TM & (GG & g & GD) & IE & SH).
  destruct STK as (ST & SK & _ & _).
  pose proof (va_small _ _ _ _ Hva) as Hsm.
  destruct (rp_model f args Hin Hk Hsm) as [PM Hrel].
  destruct (SegPrintfBridge.seg_format_good f (rp_refuse_sub f Hin)) as (_ & P1 & FB).
  assert (HN : 1 <= bv_unsigned a1 < 2 ^ 31) by (unfold RC_REFUSAL_LEN in HD2; lia).
  assert (HK : lo <= bv_unsigned sp - VSNPRINTF_K) by (unfold VSNPRINTF_K; unfold PRINTF_K in SK; lia).
  pose proof (C ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
                lo g f slots (SegPrintfBridge.sp_pargs f args) (snprintf_r f args) (fmt f args) junk) as CC.
  cbv zeta in CC.
  eapply evt_mono.
  - exact (CC (fmt_bytes _ _ _ Hz) Hlo Hhi FB P1 (saved_u64s _ _ _ SV) HVA HVB
              (va_pm_args _ _ _ _ _ _ _ _ _ HD1 HD2 Hrel Hva) PM
              (dst_cells _ _ _ _ WR BJ LJ) HN D0 AP NI ST HK IE SH FR MI TM GG GD).
  - intros ms' P. apply post_conv. exact P.
Qed.
