(* reloc-zl14c *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Lib Require Import Tac Image. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Spec Require Import Prog.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.P Require Import Z_kit.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.U Require Import Z_dview Z_drep.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZProg ZIface InflateState RefInflateSafeTY ZApiInst. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import ZTaintI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Definition Z_LENFIX : Z := 0x126de.
Definition Z_DISTFIX : Z := 0x12ede.
Definition Z_ORDER : Z := 0x125bc.
Notation ZI_SIZE := 7176 (only parsing).
Notation ZI_WIN := 32768 (only parsing).
Definition Z_IMSGS : list Z :=
  [0x10570; 0x1060b; 0x10508; 0x103df; 0x10666; 0x104cc; 0x10316; 0x1046b; 0x1067a; 0x102ba; 0x10587; 0x10392; 0x105d8;
   0x10554; 0x10351; 0x102d4; 0x10626; 0x1051c;
    0x10554; 0x10351; 0x102d4].
Definition imsg_ptr (k : Z) : Z := if k <? 10 then msg_ptr k else nth (Z.to_nat (k - 10)) Z_IMSGS 0.
Record ilay : Type := mkIL {
  il_S : Z;
  il_As : Z;
  il_Aw : Z;
  il_NI : Z;
  il_NO : Z
}.
Definition cp_addr (L : ilay) (p : codeptr) : Z :=
  match p with CDyn ofs => il_As L + 1384 + 4 * ofs | CLenfix => Z_LENFIX | CDistfix => Z_DISTFIX end.
Definition win_addr (L : ilay) (wb : option ZProg.blk) : Z :=
  match wb with Some _ => il_Aw L | None => 0 end.
Definition ilay_ok (L : ilay) (s : inflate_state) : Prop :=
  blk_ok (il_As L) ZI_SIZE
  /\ (is_window_blk s <> None -> blk_ok (il_Aw L) ZI_WIN /\ apart (il_As L) ZI_SIZE (il_Aw L) ZI_WIN).
Section Groups.
Variables (m : mem) (L : ilay) (s : inflate_state).
Definition isA_cells : list cell :=
  [C8 (wz (il_S L));
   C4 (wz (is_mode s)); C4 (wz (is_last s)); C4 (wz (is_wrap s)); C4 (wz 5);
   C4 (wz (is_havedict s)); C4 (wz (is_flags s)); C4 (wz (is_dmax s)); C4 (wz 0);
   C8 (wz (is_check s)); C8 (wz (is_total s)); C8 (wz (is_head s));
   C4 (wz 15); C4 (wz (is_wbits s)); C4 (wz (is_wsize s)); C4 (wz (is_whave s)); C4 (wz (is_wnext s)); C4 (wz 0);
   C8 (wz (win_addr L (is_window_blk s)));
   C8 (wz (is_hold s)); C4 (wz (is_bits s)); C4 (wz (is_length s)); C4 (wz (is_offset s)); C4 (wz (is_extra s));
   C8 (wz (cp_addr L (is_lencode s))); C8 (wz (cp_addr L (is_distcode s)));
   C4 (wz (is_lenbits s)); C4 (wz (is_distbits s)); C4 (wz (is_ncode s)); C4 (wz (is_nlen s)); C4 (wz (is_ndist s)); C4 (wz (is_have s));
   C8 (wz (il_As L + 1384 + 4 * is_next s))].
Definition isA : Prop := rw_cells usegs m (il_As L) isA_cells.
Definition isT_cells (pad : list byte) : list cell :=
  [C4 (wz (is_sane s)); C4 (wz (is_back s)); C4 (wz (is_was s)); CB 4 pad].
Definition isT : Prop := exists pad, rw_cells usegs m (il_As L + 7160) (isT_cells pad).
Definition ilens : Prop := u16arr usegs m (il_As L + 168) (av16 (is_lens s) 320).
Definition iwork : Prop := u16arr usegs m (il_As L + 808) (av16 (is_work s) 288).
Definition icodes : Prop := u32arr usegs m (il_As L + 1384) (av32 (is_codes s) 1444).
Definition iwin : Prop :=
  match is_window_blk s with Some _ => u8arr usegs m (il_Aw L) (av8 (is_window s) ZI_WIN) | None => True end.
End Groups.
Definition iarrs (s : inflate_state) : Prop :=
  arr_len (is_lens s) = 320 /\ arr_len (is_work s) = 288 /\ arr_len (is_codes s) = 1444
  /\ (is_window_blk s <> None -> arr_len (is_window s) = ZI_WIN).
Record IST (m : mem) (L : ilay) (s : inflate_state) : Prop := mkIST {
  ist_A : isA m L s;
  ist_T : isT m L s;
  ist_lens : ilens m L s;
  ist_work : iwork m L s;
  ist_codes : icodes m L s;
  ist_win : iwin m L s;
  ist_arrs : iarrs s;
  ist_lay : ilay_ok L s
}.
Definition izs_priv_cells (L : ilay) (msg adler : Z) (dt : word) (p3 : list byte) (resv : word) : list cell :=
  [C8 (wz (imsg_ptr msg)); C8 (wz (il_As L)); C8 (wz Z_ZCALLOC); C8 (wz Z_ZCFREE); C8 (wz 0);
   C4 dt; CB 4 p3; C8 (wz adler); C8 resv].
Definition izs_call_cells (L : ilay) (c : icall) (p1 p2 : list byte) (dt : word) (p3 : list byte) (resv : word) : list cell :=
  [C8 (wz (il_NI L + ic_next_in c)); C4 (wz (ic_avail_in c)); CB 4 p1; C8 (wz (ic_total_in c));
   C8 (wz (il_NO L + ic_next_out c)); C4 (wz (ic_avail_out c)); CB 4 p2; C8 (wz (ic_total_out c))]
  ++ izs_priv_cells L (ic_msg c) (ic_adler c) dt p3 resv.
Definition izs (m : mem) (L : ilay) (c : icall) : Prop :=
  exists p1 p2 dt p3 resv, rw_cells usegs m (il_S L) (izs_call_cells L c p1 p2 dt p3 resv).
Definition izq (m : mem) (L : ilay) (z : zstrm) : Prop :=
  exists dt p3 resv, rw_cells usegs m (il_S L + 48) (izs_priv_cells L (zs_msg z) (zs_adler z) dt p3 resv).
Definition IREP (m : mem) (L : ilay) (s : inflate_state) (c : icall) : Prop := izs m L c /\ IST m L s.
Definition IREPq (m : mem) (L : ilay) (s : inflate_state) (z : zstrm) : Prop := izq m L z /\ IST m L s.
Definition bkmax (m : Z) : Z :=
  if m =? LENEXT then 510 else if m =? DIST then 525 else if m =? DISTEXT then 1035 else 1050.
Definition bk_ok (s : inflate_state) : Prop := -1 <= is_back s <= bkmax (is_mode s).
Lemma bkmax_range : forall m, 510 <= bkmax m <= 1050.
Proof. intros m. unfold bkmax. destruct (m =? LENEXT); [lia|]. destruct (m =? DIST); [lia|]. destruct (m =? DISTEXT); lia. Qed.
Definition PATIq (s : inflate_state) : Prop :=
  is_wrap s = 5 /\ is_wbits s = 15 /\ is_head s = 0
  /\ (is_flags s = 0 \/ (is_flags s = -1 /\ (is_mode s = HEAD \/ is_mode s = BAD)))
  /\ ~ (FLAGS <= is_mode s <= HCRC)
  /\ (is_last s = 0 \/ is_last s = 1) /\ (is_havedict s = 0 \/ is_havedict s = 1)
  /\ (forall i, 0 <= i < arr_len (is_window s) -> 0 <= arr_get (is_window s) i < 256)
  /\ bk_ok s.
Section Frame.
Variables (m m' : mem) (L : ilay) (s : inflate_state).
Lemma isA_agree : isA m L s -> agree_on (il_As L) (il_As L + 168) m m' -> isA m' L s.
Proof. intros H AG. apply (rw_cells_agree m); [exact H| exact AG]. Qed.
Lemma isT_agree : isT m L s -> agree_on (il_As L + 7160) (il_As L + 7160 + 16) m m' -> isT m' L s.
Proof. intros (pad & H) AG. exists pad. apply (rw_cells_agree m); [exact H| exact AG]. Qed.
Lemma ilens_agree : ilens m L s -> agree_on (il_As L + 168) (il_As L + 168 + 640) m m' -> ilens m' L s.
Proof. intros H AG. apply (u16arr_agree m); [exact H|]. rewrite av16_length. exact AG. Qed.
Lemma iwork_agree : iwork m L s -> agree_on (il_As L + 808) (il_As L + 808 + 576) m m' -> iwork m' L s.
Proof. intros H AG. apply (u16arr_agree m); [exact H|]. rewrite av16_length. exact AG. Qed.
Lemma icodes_agree : icodes m L s -> agree_on (il_As L + 1384) (il_As L + 1384 + 5776) m m' -> icodes m' L s.
Proof. intros H AG. apply (u32arr_agree m); [exact H|]. rewrite av32_length. exact AG. Qed.
Lemma isA_munch : forall W, isA m L s -> munch W m m' -> wmono usegs m m' -> disjoint_from W (il_As L) 168 -> isA m' L s.
Proof.
  intros W H MU WM D. apply isA_agree; [exact H|]. pose proof (rw_cells_bound usegs m _ _ H) as B.
  match type of B with context [Z.of_nat ?n] => let v := eval vm_compute in (Z.of_nat n) in change (Z.of_nat n) with v in B end.
  apply (agree_on_of_munch W); [exact MU| exact WM| lia| lia| exact D].
Qed.
Lemma isT_munch : forall W, isT m L s -> munch W m m' -> wmono usegs m m' -> disjoint_from W (il_As L + 7160) 16 -> isT m' L s.
Proof.
  intros W H MU WM D. apply isT_agree; [exact H|]. destruct H as (pad & H). pose proof (rw_cells_bound usegs m _ _ H) as B.
  match type of B with context [Z.of_nat ?n] => let v := eval vm_compute in (Z.of_nat n) in change (Z.of_nat n) with v in B end.
  apply (agree_on_of_munch W); [exact MU| exact WM| lia| lia| exact D].
Qed.
Lemma ilens_munch : forall W, ilens m L s -> munch W m m' -> wmono usegs m m' -> disjoint_from W (il_As L + 168) 640 -> ilens m' L s.
Proof.
  intros W H MU WM D. apply ilens_agree; [exact H|]. pose proof (u16arr_bound m _ _ H) as B. rewrite av16_length in B.
  apply (agree_on_of_munch W); [exact MU| exact WM| lia| lia| exact D].
Qed.
Lemma iwork_munch : forall W, iwork m L s -> munch W m m' -> wmono usegs m m' -> disjoint_from W (il_As L + 808) 576 -> iwork m' L s.
Proof.
  intros W H MU WM D. apply iwork_agree; [exact H|]. pose proof (u16arr_bound m _ _ H) as B. rewrite av16_length in B.
  apply (agree_on_of_munch W); [exact MU| exact WM| lia| lia| exact D].
Qed.
Lemma icodes_munch : forall W, icodes m L s -> munch W m m' -> wmono usegs m m' -> disjoint_from W (il_As L + 1384) 5776 -> icodes m' L s.
Proof.
  intros W H MU WM D. apply icodes_agree; [exact H|]. pose proof (u32arr_bound usegs m _ _ H) as B. rewrite av32_length in B.
  apply (agree_on_of_munch W); [exact MU| exact WM| lia| lia| exact D].
Qed.
Lemma iwin_munch : forall W, iwin m L s -> munch W m m' -> wmono usegs m m' ->
  (is_window_blk s <> None -> disjoint_from W (il_Aw L) ZI_WIN) -> iwin m' L s.
Proof.
  intros W H MU WM D. unfold iwin in *. destruct (is_window_blk s) eqn:E; [|exact I].
  apply (u8arr_agree m); [exact H|]. pose proof (u8arr_bound usegs m _ _ H) as B. rewrite av8_length in *.
  apply (agree_on_of_munch W); [exact MU| exact WM| lia| lia| apply D; discriminate].
Qed.
Lemma izs_agree : forall c, izs m L c -> agree_on (il_S L) (il_S L + 112) m m' -> izs m' L c.
Proof. intros c (p1 & p2 & dt & p3 & resv & H) AG. exists p1, p2, dt, p3, resv. apply (rw_cells_agree m); [exact H| exact AG]. Qed.
Lemma izq_agree : forall z, izq m L z -> agree_on (il_S L + 48) (il_S L + 48 + 64) m m' -> izq m' L z.
Proof. intros z (dt & p3 & resv & H) AG. exists dt, p3, resv. apply (rw_cells_agree m); [exact H| exact AG]. Qed.
Lemma izs_munch : forall W c, izs m L c -> munch W m m' -> wmono usegs m m' -> disjoint_from W (il_S L) 112 -> izs m' L c.
Proof.
  intros W c H MU WM D. apply izs_agree; [exact H|]. destruct H as (p1 & p2 & dt & p3 & resv & H). pose proof (rw_cells_bound usegs m _ _ H) as B.
  match type of B with context [Z.of_nat ?n] => let v := eval vm_compute in (Z.of_nat n) in change (Z.of_nat n) with v in B end.
  apply (agree_on_of_munch W); [exact MU| exact WM| lia| lia| exact D].
Qed.
Definition iag_blocks : Prop :=
  agree_on (il_As L) (il_As L + ZI_SIZE) m m' /\ (is_window_blk s <> None -> agree_on (il_Aw L) (il_Aw L + ZI_WIN) m m').
Lemma IST_agree : IST m L s -> iag_blocks -> IST m' L s.
Proof.
  intros [HA HT Hl Hw Hc Hwin Harr Hlay] (A0 & A1).
  assert (G : forall lo hi, il_As L <= lo -> hi <= il_As L + 7176 -> agree_on lo hi m m') by (intros lo hi H1 H2; eapply agree_on_sub; [exact A0| lia| lia]).
  constructor.
  - apply isA_agree; [assumption| apply G; lia].
  - apply isT_agree; [assumption| apply G; lia].
  - apply ilens_agree; [assumption| apply G; lia].
  - apply iwork_agree; [assumption| apply G; lia].
  - apply icodes_agree; [assumption| apply G; lia].
  - unfold iwin in *. destruct (is_window_blk s) eqn:E; [|exact I].
    apply (u8arr_agree m); [exact Hwin|]. rewrite av8_length. apply A1. discriminate.
  - assumption.
  - assumption.
Qed.
Lemma IREPq_agree : forall z, IREPq m L s z -> iag_blocks -> agree_on (il_S L + 48) (il_S L + 112) m m' -> IREPq m' L s z.
Proof.
  intros z [Z D] AB AS. split; [eapply izq_agree; [exact Z|]| apply IST_agree; assumption].
  eapply agree_on_sub; [exact AS| lia| lia].
Qed.
End Frame.
Definition iblk_list (w : option bptr) (Aw : Z) (sp_ : bptr) (As : Z) : list block :=
  match w with Some wp => [(wp, Aw, ZI_WIN)] | None => [] end ++ [(sp_, As, ZI_SIZE)].
Definition zr_i_def (m : mem) (S : Z) (LBz : list block) (x : istream) : Prop :=
  exists (s_a : inflate_state) (L : ilay) (w : option bptr) (sp_ : bptr),
    il_S L = S
    /\ LBz = iblk_list w (il_Aw L) sp_ (il_As L)
    /\ (w = None <-> is_window_blk s_a = None)
    /\ IREPq m L s_a (iz_z x)
    /\ IREL s_a x
    /\ ATY s_a
    /\ PATIq s_a.
Lemma zr_i_def_frame : forall m m' S LBz x, zr_i_def m S LBz x ->
  (forall a, 0 <= a < 2^64 -> (S + 48 <= a < S + 112 \/ in_block LBz a) ->
     m' (wa a) = m (wa a) /\ (wview usegs m (wa a) <> None -> wview usegs m' (wa a) <> None)) ->
  zr_i_def m' S LBz x.
Proof.
  intros m m' S LBz x (s_a & L & w & sp_ & ES & EL & HW & HR & HI & HRe & HP) AG.
  exists s_a, L, w, sp_. repeat (split; [assumption|]). split; [|repeat (split; [assumption|]); assumption].
  pose proof HR as [HZ HS]. pose proof (ist_lay _ _ _ HS) as [(s1 & _ & s2 & _) HLW].
  apply (IREPq_agree m); [exact HR| |].
  - split.
    + intros a Ha. apply AG; [lia|]. right. subst LBz. exists (sp_, il_As L, 7176). split.
      * unfold iblk_list. apply in_or_app. right. left. reflexivity.
      * unfold blk_addr, blk_size. cbn [fst snd]. lia.
    + intros NE. destruct (HLW NE) as [(w1 & _ & w2 & _) _]. destruct w as [wp|]; [|exfalso; apply NE; apply HW; reflexivity].
      intros a Ha. apply AG; [lia|]. right. subst LBz. exists (wp, il_Aw L, 32768). split.
      * unfold iblk_list. apply in_or_app. left. left. reflexivity.
      * unfold blk_addr, blk_size. cbn [fst snd]. lia.
  - destruct HZ as (dt & p3 & resv & HZ). pose proof (rw_cells_bound usegs m _ _ HZ) as B.
    match type of B with context [Z.of_nat ?n] => let v := eval vm_compute in (Z.of_nat n) in change (Z.of_nat n) with v in B end.
    intros a Ha. apply AG; [lia|]. left. lia.
Qed.
Lemma zr_i_def_stream : forall m S LBz x, zr_i_def m S LBz x -> exists j : list byte, rw_cells usegs m (S + 48) [CB 64 j].
Proof.
  intros m S LBz x (s_a & L & w & sp_ & ES & _ & _ & [(dt & p3 & resv & HZ) _] & _). subst S.
  destruct (rw_cells_forget usegs m _ _ HZ) as (j & Hj). exists j. exact Hj.
Qed.
