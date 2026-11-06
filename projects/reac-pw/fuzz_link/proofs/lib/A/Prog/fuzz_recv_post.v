(* fuzz_recv on image A: the two Posts of its walk (lib/A/Prog/fuzz_recv_defs.v RV_CPOST, RV_FPOST), from what each
   arm leaves in memory. No instruction runs here.
   - rvp_gnl: the end memory's g_nl list bs' (LinkWalkNlk.v anlk_after over the window [NK_NEXT, NK_MISUSE + 4)):
     every byte but next and misuse is the call's (rv_inv's kept clause: g_nl lies below the frame window and apart
     from the buffer and errno), so every field but those two reads as at the call, and nlk_wf bs' holds
     (nlk_wf_same_queues); next and misuse read the values the arm stored.
   - rvp_abuf: the buffer is readable (every byte defined) and writable (its bytes were writable at the call and are
     still present).
   - rv_cpost_ok: the chunk arm; the buffer starts with the chunk (rv_cmem's copy clause and g_nl's bytes at the
     call), then the bytes of [buf + clen, buf + len) as they are.
   - rv_fpost_ok: the failure arm.
   Proves no function (kind: segment lemma). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16 YG0s YA0d YA0j.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import YC4b.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
link_aaddr link_amem LinkWalk LinkWalkNlk fuzz_recv_c fuzz_recv_defs fuzz_recv_kit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

(* lia with g_nl's layout constants as numbers *)
Ltac rvlia :=
  unfold NK_CHUNK, NL_CHUNK_MAX, NL_CHUNKS, NL_SENT_MAX, NK_SIZE, NK_CHUNK_LEN, NK_N_CHUNKS, NK_NEXT,
    NK_END_ERRNO, NK_SOCKET_ERRNO, NK_SEND_ERRNO, NK_OPEN, NK_OPENED, NK_CLOSED, NK_MISUSE, NK_SENT_LEN,
    NK_N_SENT, NK_N_IF, LA_G_NL in *;
  lia.
(* a 4-byte read of anlk_after's third conjunct *)
Ltac rvn4 := try change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32); try change (Z.of_nat 4) with 4.

Lemma rvp_win_dec : forall i a, {a <= i < a + 4} + {~ (a <= i < a + 4)}.
Proof.
  intros i a. destruct (Z_lt_le_dec i a) as [H1|H1]; [|destruct (Z_lt_le_dec i (a + 4)) as [H2|H2]].
  - right; lia.
  - left; lia.
  - right; lia.
Qed.

Lemma rvp_val_mem4_some : forall segs m a v, val_mem segs m a 4 v ->
  forall j, a <= j < a + 4 -> exists b, mbyte segs m j = Some b.
Proof.
  intros segs m a v H j Hj.
  pose proof (H (Z.to_nat (j - a)) ltac:(lia)) as Hb.
  replace (a + Z.of_nat (Z.to_nat (j - a))) with j in Hb by lia.
  eexists; exact Hb.
Qed.

(* two equal views are two equal bytes, at any two addresses *)
Lemma rvp_mbyte_eq : forall segs H H' (m m' : word -> option byte) a a',
  aview segs H' m' a' = aview segs H m a -> mbyte segs (mrestrict H' m') a' = mbyte segs (mrestrict H m) a.
Proof.
  intros segs H H' m m' a a' E. unfold aview in E.
  destruct (mbyte segs (mrestrict H' m') a') as [b'|], (mbyte segs (mrestrict H m) a) as [b|];
    cbn in E; try discriminate; [|reflexivity].
  injection E as E. f_equal. apply bv_eq. exact E.
Qed.

Lemma rvp_mbyte_some : forall segs H (m : word -> option byte) a,
  aview segs H m a <> None -> exists b, mbyte segs (mrestrict H m) a = Some b.
Proof.
  intros segs H m a Hv. unfold aview in Hv.
  destruct (mbyte segs (mrestrict H m) a) as [b|]; [exists b; reflexivity | exfalso; apply Hv; reflexivity].
Qed.

(* the n bytes of a list from off are the same list, when those bytes did not change *)
Lemma rvp_slice_agree : forall (l l' : list byte) off n,
  0 <= off -> 0 <= n -> off + n <= Z.of_nat (length l) -> off + n <= Z.of_nat (length l') ->
  (forall k, (k < Z.to_nat n)%nat -> nth_error l' (Z.to_nat off + k) = nth_error l (Z.to_nat off + k)) ->
  slice l' off n = slice l off n.
Proof.
  intros l l' off n Hoff Hn Hl Hl' H. apply lw_list_ext.
  - rewrite !lw_slice_length by lia. reflexivity.
  - intros k Hk. rewrite lw_slice_length in Hk by lia. rewrite !lw_slice_nth by lia. exact (H k Hk).
Qed.

Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Context {PI : PAImg link_listing}.
#[local] Abbreviation SEGS := (@pa_segs _ link_listing PI).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Variable c : rvc.
Hypothesis HC : rv_call SK B c.
#[local] Abbreviation W := (c_W c).
#[local] Abbreviation memc := (c_memc c).
#[local] Abbreviation bs := (c_bs c).

(* THE END MEMORY'S g_nl LIST: every field but next and misuse as at the call *)
Lemma rvp_gnl : forall regs mem md vn,
  rv_inv SK B c regs mem md ->
  val_mem SEGS (rdW W mem) (LA_G_NL + NK_NEXT) 4 vn -> 0 <= vn <= nk_n_chunks bs ->
  val_mem SEGS (rdW W mem) (LA_G_NL + NK_MISUSE) 4 (rv_msu c) ->
  exists bs', anlk_at SEGS (rdW W mem) LA_G_NL bs' /\ nlk_wf bs' /\
    nk_n_chunks bs' = nk_n_chunks bs /\ nk_end_errno bs' = nk_end_errno bs /\
    nk_socket_errno bs' = nk_socket_errno bs /\ nk_send_errno bs' = nk_send_errno bs /\
    nk_chunks bs' = nk_chunks bs /\ nk_open bs' = nk_open bs /\ nk_opened bs' = nk_opened bs /\
    nk_closed bs' = nk_closed bs /\ nk_n_sent bs' = nk_n_sent bs /\ nk_misuse bs' = rv_msu c /\
    nk_next bs' = vn.
Proof.
  intros regs mem md vn (_ & _ & _ & _ & _ & _ & _ & _ & _ & UN & PR) Vnx Hvn Vmi.
  pose proof HC as (_ & HNK & WF & _ & _ & _ & _ & _ & _ & Hegn & _ & _ & _ & _ & _ & _ & Hbgn & _).
  pose proof (rv_sp_bounds SK B c HC) as (Hceil & Hlo & _).
  pose proof asan_consts as ((C1a & C1b) & _).
  pose proof HNK as [[(Hg0 & Hgl & Hab) Hwr] HL].
  pose proof WF as (Wnc & Wnx & Wns & Wni & Wop & Won & Wcl & Wmi & Wee & Wse & Wsd & Wcln & Wsln).
  (* a byte of g_nl outside next and misuse is the call's *)
  assert (Hun : forall i, 0 <= i < NK_SIZE -> ~ (NK_NEXT <= i < NK_NEXT + 4) -> ~ (NK_MISUSE <= i < NK_MISUSE + 4) ->
            mbyte SEGS (rdW W mem) (LA_G_NL + i) = mbyte SEGS (rdW W memc) (LA_G_NL + i)).
  { intros i Hi Hn Hm. apply (rvp_mbyte_eq SEGS). apply UN.
    - rvlia.
    - rvlia.
    - unfold rv_ewr, rv_buf, rv_len. unfold apart_gnl in Hbgn, Hegn. rvlia. }
  assert (Hcall : forall i, 0 <= i < NK_SIZE -> mbyte SEGS (rdW W memc) (LA_G_NL + i) = nth_error bs (Z.to_nat i)).
  { intros i Hi. rewrite <- (Hab (Z.to_nat i)) by lia. rewrite Z2Nat.id by lia. reflexivity. }
  (* every byte of g_nl is defined at the end *)
  assert (Hex : forall i, 0 <= i < NK_SIZE -> exists b, mbyte SEGS (rdW W mem) (LA_G_NL + i) = Some b).
  { intros i Hi.
    destruct (rvp_win_dec i NK_NEXT) as [Hw1|Hw1];
      [exact (rvp_val_mem4_some _ _ _ _ Vnx (LA_G_NL + i) ltac:(lia))|].
    destruct (rvp_win_dec i NK_MISUSE) as [Hw2|Hw2];
      [exact (rvp_val_mem4_some _ _ _ _ Vmi (LA_G_NL + i) ltac:(lia))|].
    rewrite (Hun i Hi Hw1 Hw2), (Hcall i Hi).
    destruct (nth_error bs (Z.to_nat i)) as [b|] eqn:E; [exists b; reflexivity|].
    apply nth_error_None in E. lia. }
  assert (Hout : forall i, 0 <= i < NK_SIZE -> ~ (NK_NEXT <= i < NK_MISUSE + 4) ->
            mbyte SEGS (rdW W mem) (LA_G_NL + i) = mbyte SEGS (rdW W memc) (LA_G_NL + i)).
  { intros i Hi Hw. apply Hun; [exact Hi | |]; unfold NK_NEXT, NK_MISUSE in Hw |- *; lia. }
  assert (Hin : forall i, 0 <= i < NK_SIZE -> NK_NEXT <= i < NK_MISUSE + 4 ->
            exists b, mbyte SEGS (rdW W mem) (LA_G_NL + i) = Some b)
    by (intros i Hi _; exact (Hex i Hi)).
  assert (Hwr' : forall i, 0 <= i < NK_SIZE -> writable_at SEGS (rdW W mem) (LA_G_NL + i)).
  { intros i Hi. apply (writable_kept (segs := SEGS) (w_H W) memc mem); [exact (PR _) | apply Hwr; lia]. }
  destruct (anlk_after SEGS (rdW W memc) (rdW W mem) LA_G_NL bs NK_NEXT (NK_MISUSE + 4) HNK Hout Hin Hwr')
    as (HNK' & _ & Hrd_val).
  set (bs' := abytes_of SEGS (rdW W mem) LA_G_NL (Z.to_nat NK_SIZE)) in *.
  assert (Hsame : forall i, 0 <= i < NK_SIZE -> ~ (NK_NEXT <= i < NK_NEXT + 4) ->
            ~ (NK_MISUSE <= i < NK_MISUSE + 4) -> nth_error bs' (Z.to_nat i) = nth_error bs (Z.to_nat i)).
  { intros i Hi Hn Hm. rewrite <- (Hcall i Hi), <- (Hun i Hi Hn Hm).
    destruct (Hex i Hi) as (b & Eb). rewrite Eb.
    unfold bs'. apply (abytes_of_nth SEGS); [lia|]. rewrite Z2Nat.id by lia. exact Eb. }
  assert (Fsame : forall off n, 0 <= off -> 0 <= n -> off + n <= NK_SIZE ->
            (off + n <= NK_NEXT \/ NK_MISUSE + 4 <= off \/ (NK_NEXT + 4 <= off /\ off + n <= NK_MISUSE)) ->
            rdn bs' off n = rdn bs off n).
  { intros off n H0 H1 H2 H3. apply rdn_agree; [lia | lia | lia | unfold bs'; rewrite abytes_of_length; lia |].
    intros k Hk. replace (Z.to_nat off + k)%nat with (Z.to_nat (off + Z.of_nat k)) by lia.
    apply Hsame; rvlia. }
  assert (Rmi : 0 <= rv_msu c <= 1)
    by (unfold rv_msu; match goal with |- context [if ?b then _ else _] => destruct b end; cbv iota; lia).
  assert (Fmi : nk_misuse bs' = rv_msu c).
  { unfold nk_misuse, fld_u32. refine (Hrd_val NK_MISUSE 4%nat (rv_msu c) _ _ _ Vmi); rvn4; rvlia. }
  assert (Fnx : nk_next bs' = vn).
  { unfold nk_next, fld_u32. refine (Hrd_val NK_NEXT 4%nat vn _ _ _ Vnx); rvn4; rvlia. }
  assert (Fnc : nk_n_chunks bs' = nk_n_chunks bs) by (unfold nk_n_chunks, fld_u32; apply Fsame; rvlia).
  assert (Fee : nk_end_errno bs' = nk_end_errno bs) by (unfold nk_end_errno, fld_u32; apply Fsame; rvlia).
  assert (Fse : nk_socket_errno bs' = nk_socket_errno bs) by (unfold nk_socket_errno, fld_u32; apply Fsame; rvlia).
  assert (Fsd : nk_send_errno bs' = nk_send_errno bs) by (unfold nk_send_errno, fld_u32; apply Fsame; rvlia).
  assert (Fop : nk_open bs' = nk_open bs) by (unfold nk_open, fld_u32; apply Fsame; rvlia).
  assert (Fon : nk_opened bs' = nk_opened bs) by (unfold nk_opened, fld_u32; apply Fsame; rvlia).
  assert (Fcl : nk_closed bs' = nk_closed bs) by (unfold nk_closed, fld_u32; apply Fsame; rvlia).
  assert (Fns : nk_n_sent bs' = nk_n_sent bs) by (unfold nk_n_sent, fld_u32; apply Fsame; rvlia).
  assert (Fni : nk_n_if bs' = nk_n_if bs) by (unfold nk_n_if, fld_u32; apply Fsame; rvlia).
  assert (Fcl64 : forall i, 0 <= i < nk_n_chunks bs ->
            fld_u64 bs' (NK_CHUNK_LEN + 8 * i) = fld_u64 bs (NK_CHUNK_LEN + 8 * i))
    by (intros i Hi; unfold fld_u64; apply Fsame; rvlia).
  assert (Fsl64 : forall i, 0 <= i < nk_n_sent bs ->
            fld_u64 bs' (NK_SENT_LEN + 8 * i) = fld_u64 bs (NK_SENT_LEN + 8 * i))
    by (intros i Hi; unfold fld_u64; apply Fsame; rvlia).
  (* the chunk queue: the lengths and the chunk area lie below next *)
  assert (Fch : nk_chunks bs' = nk_chunks bs).
  { unfold nk_chunks. rewrite Fnc. apply map_ext_in. intros i Hi. apply in_seq in Hi.
    unfold nk_chunk. rewrite (Fcl64 (Z.of_nat i)) by lia.
    pose proof (Wcln (Z.of_nat i) ltac:(lia)) as Hcl.
    apply rvp_slice_agree; [rvlia | lia | rvlia | unfold bs'; rewrite abytes_of_length; rvlia |].
    intros k Hk. replace (Z.to_nat (NK_CHUNK + NL_CHUNK_MAX * Z.of_nat i) + k)%nat
      with (Z.to_nat (NK_CHUNK + NL_CHUNK_MAX * Z.of_nat i + Z.of_nat k)) by rvlia.
    apply Hsame; rvlia. }
  assert (WF' : nlk_wf bs').
  { apply (nlk_wf_same_queues bs bs' WF Fnc Fns Fni Fcl64 Fsl64).
    - rewrite Fnx. lia.
    - rewrite Fop. lia.
    - rewrite Fon. lia.
    - rewrite Fcl. lia.
    - rewrite Fmi. lia.
    - rewrite Fee. lia.
    - rewrite Fse. lia.
    - rewrite Fsd. lia. }
  exists bs'.
  exact (conj HNK' (conj WF' (conj Fnc (conj Fee (conj Fse (conj Fsd (conj Fch (conj Fop (conj Fon
    (conj Fcl (conj Fns (conj Fmi Fnx)))))))))))).
Qed.

(* THE BUFFER at the end: every byte defined, every byte writable *)
Lemma rvp_abuf : forall regs mem md, rv_inv SK B c regs mem md ->
  (forall i, 0 <= i < rv_len c -> aview SEGS (w_H W) mem (rv_buf c + i) <> None) ->
  abuf SEGS (rdW W mem) (aarg (c_regs0 c) 1) (aarg (c_regs0 c) 2).
Proof.
  intros regs mem md (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PR) Hdef.
  pose proof HC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hlen & Hb0 & (junk & Hjl & _ & Hjw) & Hamr & _).
  pose proof asan_consts as (_ & _ & _ & C4 & C5).
  unfold rv_buf, rv_len in Hdef. unfold amem_range in Hamr. unfold NL_CHUNK_MAX in Hlen.
  exists (abytes_of SEGS (rdW W mem) (aarg (c_regs0 c) 1) (Z.to_nat (aarg (c_regs0 c) 2))).
  rewrite abytes_of_length. split; [lia|]. split.
  - apply abytes_of_abytes; [lia | lia |].
    intros i Hi. apply rvp_mbyte_some. exact (Hdef (Z.of_nat i) ltac:(lia)).
  - intros i Hi. rewrite abytes_of_length in Hi.
    apply (writable_kept (segs := SEGS) (w_H W) memc mem); [exact (PR _) | apply Hjw; lia].
Qed.

(* THE CHUNK ARM *)
Lemma rv_cpost_ok : RV_CPOST SK B c.
Proof.
  intros regs mem md regs2 HI (Hcp & Hdef & Vnx & Vmi) Hlt R10.
  pose proof HC as (_ & HNK & WF & _ & _ & _ & _ & _ & _ & _ & Hlen & Hb0 & _ & Hamr & _).
  pose proof WF as (Wnc & Wnx & _ & _ & _ & _ & _ & _ & _ & _ & _ & Wcln & _).
  pose proof HNK as [[(Hg0 & Hgl & Hab) _] HL].
  pose proof asan_consts as (_ & _ & _ & C4 & C5).
  assert (Hbe : aarg (c_regs0 c) 1 + aarg (c_regs0 c) 2 <= 2 ^ 64) by (unfold amem_range in Hamr; lia).
  unfold rv_clen, rv_next, rv_buf, rv_len in Hcp, Hdef, Vnx, R10.
  assert (Hcl : 0 <= fld_u64 bs (NK_CHUNK_LEN + 8 * nk_next bs) <= NL_CHUNK_MAX) by (apply Wcln; lia).
  assert (Lc : length (nk_chunk bs (nk_next bs)) = Z.to_nat (fld_u64 bs (NK_CHUNK_LEN + 8 * nk_next bs))).
  { unfold nk_chunk. apply lw_slice_length; rvlia. }
  unfold fuzz_recv_apost. split.
  - intros bs0 H0. rewrite (anlk_at_unique SEGS _ _ bs0 bs H0 HNK). clear bs0 H0.
    destruct (rvp_gnl regs mem md (nk_next bs + 1) HI Vnx ltac:(lia) Vmi)
      as (bs' & HNK' & WF' & E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & Emi & Enx).
    exists bs'.
    refine (conj HNK' (conj WF' (conj E1 (conj E2 (conj E3 (conj E4 (conj E5 (conj E6 (conj E7 (conj E8
      (conj E9 (conj Emi (conj _ _))))))))))))).
    + intros Hge. exfalso. lia.
    + intros _. cbv zeta. split; [rewrite Lc, Z2Nat.id by lia; exact R10|]. split; [exact Enx|].
      set (rest := abytes_of SEGS (rdW W mem) (aarg (c_regs0 c) 1 + fld_u64 bs (NK_CHUNK_LEN + 8 * nk_next bs))
                     (Z.to_nat (aarg (c_regs0 c) 2 - fld_u64 bs (NK_CHUNK_LEN + 8 * nk_next bs)))).
      assert (Lr : length rest = Z.to_nat (aarg (c_regs0 c) 2 - fld_u64 bs (NK_CHUNK_LEN + 8 * nk_next bs)))
        by apply abytes_of_length.
      exists rest. split; [|rewrite Lr, Lc; lia].
      split; [lia|]. rewrite length_app, Lc, Lr. split; [rvlia|].
      intros i Hi.
      destruct (Nat.lt_ge_cases i (Z.to_nat (fld_u64 bs (NK_CHUNK_LEN + 8 * nk_next bs)))) as [Hi1|Hi1].
      * (* the chunk: the copy of g_nl's bytes at the call *)
        rewrite nth_error_app1 by (rewrite Lc; exact Hi1).
        unfold nk_chunk. rewrite lw_slice_nth by rvlia.
        rewrite (rvp_mbyte_eq SEGS _ _ _ _ _ _ (Hcp (Z.of_nat i) ltac:(lia))).
        rewrite <- (Hab (Z.to_nat (NK_CHUNK + NL_CHUNK_MAX * nk_next bs) + i)%nat) by rvlia.
        f_equal. rvlia.
      * (* the rest of the buffer, as it is *)
        rewrite nth_error_app2 by (rewrite Lc; exact Hi1). rewrite Lc.
        destruct (rvp_mbyte_some SEGS _ _ _ (Hdef (Z.of_nat i) ltac:(lia))) as (b & Eb).
        rewrite Eb. symmetry. unfold rest. apply (abytes_of_nth SEGS); [lia|].
        rewrite <- Eb. f_equal. lia.
  - exact (rvp_abuf regs mem md HI Hdef).
Qed.

(* THE FAILURE ARM *)
Lemma rv_fpost_ok : RV_FPOST SK B c.
Proof.
  intros regs mem md regs2 HI Hge Vnx Vmi Herr Hdef R10.
  pose proof HC as (_ & HNK & WF & _).
  pose proof WF as (Wnc & Wnx & _).
  unfold fuzz_recv_apost. split.
  - intros bs0 H0. rewrite (anlk_at_unique SEGS _ _ bs0 bs H0 HNK). clear bs0 H0.
    destruct (rvp_gnl regs mem md (nk_next bs) HI Vnx ltac:(lia) Vmi)
      as (bs' & HNK' & WF' & E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & Emi & Enx).
    exists bs'.
    refine (conj HNK' (conj WF' (conj E1 (conj E2 (conj E3 (conj E4 (conj E5 (conj E6 (conj E7 (conj E8
      (conj E9 (conj Emi (conj _ _))))))))))))).
    + intros _. exact (conj R10 (conj Enx Herr)).
    + intros Hlt. exfalso. lia.
  - exact (rvp_abuf regs mem md HI Hdef).
Qed.
End w.
