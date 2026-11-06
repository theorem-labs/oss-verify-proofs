From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import PropExec MState Mem Cells Exec Frame Step Tac Bytes ZBridge.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import StdioModel StdioKB memset_c __ofl_add_c fmemopen_pro.
Import ListNotations.
Open Scope Z_scope.

Definition zc272 : list cell :=
  [ C4 (wz 0); C4 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0);
    C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0);
    C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0);
    C8 (wz 0); C8 (wz 0);
    C4 (wz 0); C4 (wz 0); C8 (wz 0); C4 (wz 0); C4 (wz 0); C4 (wz 0); C4 (wz 0);
    C8 (wz 0);
    C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0);
    C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C4 (wz 0); C4 (wz 0) ].

Lemma zc272_bytes : cells_bytes zc272 = repeat (Z_to_bv 8 0) 272.
Proof. vm_compute. reflexivity. Qed.

Lemma zc272_wf : cells_wf zc272.
Proof. vm_compute. tauto. Qed.

Lemma zc272_size : cells_size zc272 = 272%nat.
Proof. reflexivity. Qed.

(* The FILE block as fmemopen leaves it for mode "w" (link's caller): flags F_NORD (4), the cookie's pos = len = 0
   (memset), size = n, buf = b, mode = 'w' (119); prev = next = 0 (__ofl_add on an empty list); the 8 unget bytes
   and the 1024-byte buffer as malloc gave them. pcap's walk ("rb") left flags F_NOWR and len = size. *)
Definition mfw_pre (h : Z) : list cell := mf_pre h (wz 4) (wz 0) (wz 0) (wz 0).

Definition mfw_post (h b n : Z) (ung buf : list byte) : list cell :=
  [ C4 (wz 4294967295); C4 (wz 0); C8 (wz 0); C4 (wz 0); C4 (wz 4294967295); C4 (wz 4294967295); C4 (wz 0);
    C8 (wz (h + 232));
    C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0);
    C8 (wz 0); C8 (wz 0); C8 (wz n); C8 (wz b); C4 (wz 119); C4 (wz 0);
    CB 8 ung; CB 1024 buf ].

Definition mfw_cells (h b n : Z) (ung buf : list byte) : list cell :=
  mfw_pre h ++ [C8 (wz 0); C8 (wz 0)] ++ mfw_post h b n ung buf.

Lemma mfw_split : forall m h b n ung buf,
  rw_cells rsegs m h (mfw_cells h b n ung buf) <->
  rw_cells rsegs m h (mfw_pre h) /\ rw_cells rsegs m (h + 104) [C8 (wz 0); C8 (wz 0)] /\
  rw_cells rsegs m (h + 120) (mfw_post h b n ung buf).
Proof.
  intros. unfold mfw_cells. rewrite !rw_cells_app. cbn [cells_size csize mfw_pre mf_pre Nat.add].
  replace (h + Z.of_nat 104 + Z.of_nat 16) with (h + 120) by lia.
  replace (h + Z.of_nat 104) with (h + 104) by lia. tauto.
Qed.

Lemma fmemopen_tail : memset_contract -> __ofl_add_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo h b n : Z) (junk : list byte)
         (r4 r3 r2 r1 r0 R : word),
    a0 = wz h -> 0 < h -> h mod 16 = 0 ->
    s1 = wz b -> s2 = wz n -> s3 = wz 0x10564 -> s4 = wz 0 ->
    0 < b < 2 ^ 64 ->
    rw_cells rsegs m h [CB 1304 junk] ->
    rw_cells rsegs m (bv_unsigned sp) [C8 r4; C8 r3; C8 r2; C8 r1; C8 r0; C8 R] ->
    stk rsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp -> 0x97000 <= lo -> bv_unsigned sp + 48 < 2 ^ 63 ->
    h + 1304 <= lo ->
    (h + 1304 <= A_LIBC \/ A_OFL_HEAD + 8 <= h) ->
    (h + 1304 <= 0x10564 \/ 0x10566 <= h) ->
    stdio_ok m -> ofl_empty m -> mem_inv rsegs m ->
    evt rsegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
        ms' = MS (mkR R (Z_to_bv 64 (bv_unsigned sp + 48)) gp tp t0' t1' t2' r0 r1 (wz h) a1' a2' a3' a4' a5' a6' a7'
                      r2 r3 r4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc R) fc None m' (seg_rom rsegs)
        /\ munch [(bv_unsigned sp, bv_unsigned sp + 48); (h, h + 1304); (A_OFL_HEAD, A_OFL_HEAD + 8)] m m'
        /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp + 48)
        /\ (exists ung buf, length ung = 8%nat /\ length buf = 1024%nat /\ rw_cells rsegs m' h (mfw_cells h b n ung buf))
        /\ ofl_one m' h /\ stdio_ok m')
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1933c) fc None m (seg_rom rsegs)).
Proof.
  intros HMEMSET HOFLADD ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo h b n junk r4 r3 r2 r1 r0 R EA0 H0 H16 ES1 ES2 ES3 ES4 B0 BLK FR ST LS L5 S63 LH DL DM HSO HE MI.
  subst a0 s1 s2 s3 s4.
  unfold memset_contract in HMEMSET. unfold __ofl_add_contract in HOFLADD.
  destruct HSO as [HT [HN HL]]. unfold ofl_empty in HE.
  unfold A_LIBC, A_OFL_LOCK, A_OFL_HEAD, wz in *.
  replace (0x95898 + 3) with 0x9589b in HN by reflexivity.
  replace (0x95898 + 1) with 0x95899 in HT by reflexivity.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  pose proof (rw_cells_bound _ _ _ _ BLK) as BH. cbn [cells_size csize] in BH.
  assert (JL : length junk = 1304%nat) by (destruct BLK as [[[HW _] _] _]; exact HW).
  pose proof (munch_refl [(bv_unsigned sp, bv_unsigned sp + 48); (h, h + 1304); (0x95cc8, 0x95cc8 + 8)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  apply (rw_cells_split_CB rsegs m h [] 1304 junk [] [272%nat; 8%nat; 1024%nat]) in BLK; [|reflexivity].
  cbn [app mk_CB_cells] in BLK.
  apply (proj1 (rw_cells_app m h [CB 272 (firstn 272 junk)] _)) in BLK. destruct BLK as [B272 BREST].
  cbn [cells_size csize] in BREST.
  assert (NZ : bv_eqb (Z_to_bv 64 h) (Z_to_bv 64 0) = false).
  { unfold bv_eqb. rewrite (unsigned_lit h) by lia. apply Z.eqb_neq. rewrite unsigned_lit by lia. lia. }
  assert (NZ' : negb (bv_eqb (Z_to_bv 64 h) (Z_to_bv 64 0)) = true) by (rewrite NZ; reflexivity).
  zstep. rewrite NZ'. cbv iota.
  zstep. zstep. zstep. zstep.
  assert (UH : bv_unsigned (Z_to_bv 64 h) = h) by (apply unsigned_lit; lia).
  assert (U272 : bv_unsigned (Z_to_bv 64 272) = 272) by reflexivity.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut; [eapply HMEMSET with (junk := firstn 272 junk);
                       [ rewrite (unsigned_lit h) by lia; rewrite (unsigned_lit 272) by lia; exact B272 | eassumption ]
                    | unfold memset_post; post_call rsegs mm] end.
  match goal with H : rw_cells _ _ (bv_unsigned (Z_to_bv 64 h)) [CB _ (repeat _ _)] |- _ =>
    rewrite UH in H; rename H into Z272 end.
  apply (rw_cells_bytes_eq _ _ _ zc272) in Z272; [ | exact zc272_wf | rewrite zc272_bytes; vm_compute; reflexivity ].
  assert (NZb : negb (bv_eqb (Z_to_bv 64 b) (Z_to_bv 64 0)) = true).
  { cbn [negb]. unfold bv_eqb. rewrite (unsigned_lit b) by lia. replace (bv_unsigned (Z_to_bv 64 0)) with 0 by reflexivity.
    destruct (Z.eqb_spec b 0); [lia | reflexivity]. }
  unfold zc272 in Z272.
  zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
  zstep. rewrite NZb. cbv iota.
  zstep. zstep.
  match goal with H : mem_inv rsegs _ |- _ => pose proof (mode_bytes_w _ H) as BM0 end. cbn [MODE_STR app] in BM0.
  zstep. zstep.
  zstep. if_false.
  zstep. zstep. zstep. if_false.
  zstep. zstep. zstep.
  zstep. zstep. zstep. if_false.
  zstep. zstep. if_true.
  zstep. if_true.
  zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (RDT : ov_read_bytes rsegs mm (Z_to_bv 64 612505) 1 = Some [Z_to_bv 8 0]) end.
  { change (Z_to_bv 64 612505) with (wa (612505 + 0)).
    rewrite (bytes_at_read rsegs _ 612505 [Z_to_bv 8 0] 0 1 HT ltac:(lia)) by (cbn; lia). reflexivity. }
  zstep.
  zstep. zstep. zstep. zstep.
  zstep. if_false.
  zstep. zstep.
  zstep.
  match goal with H : rw_cells _ _ h (C4 (Z_to_bv 64 4) :: _) |- _ => rename H into ZC end.
  replace (h + Z.of_nat (272 + 0)) with (h + 272) in BREST by lia.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
  assert (MF : rw_cells rsegs mm h (mfw_cells h b n (firstn 8 (skipn 272 junk)) (firstn 1024 (skipn 8 (skipn 272 junk))))) end.
  { match type of ZC with rw_cells _ ?mm0 h ?cs0 =>
      assert (ZB : rw_cells rsegs mm0 h (cs0 ++ [CB 8 (firstn 8 (skipn 272 junk)); CB 1024 (firstn 1024 (skipn 8 (skipn 272 junk)))])) end.
    { apply rw_cells_app. split; [exact ZC|]. cbn [cells_size csize Nat.add].
      replace (h + Z.of_nat 272) with (h + 272) by lia. exact BREST. }
    eapply rw_cells_bytes_eq; [exact ZB | |].
    - cbn [cells_wf cell_wf mfw_cells mfw_pre mf_pre mfw_post app]. rewrite !firstn_length, !skipn_length, JL. cbn. tauto.
    - assert (LE4M1 : le4 (Z_to_bv 64 (-1)) = le4 (wz 4294967295)).
      { unfold le4, wz. rewrite !Z_to_bv_unsigned.
        rewrite <- (Z_to_le_bytes_mod 4 (bv_wrap 64 (-1)) 32) by (cbn; lia).
        rewrite <- (Z_to_le_bytes_mod 4 (bv_wrap 64 4294967295) 32) by (cbn; lia).
        reflexivity. }
      cbn [cells_bytes cbytes mfw_cells mfw_pre mf_pre mfw_post app]. rewrite !LE4M1. reflexivity. }
  apply mfw_split in MF. destruct MF as (PRE & LNK & POST). unfold mfw_pre, mf_pre in PRE. unfold mfw_post in POST.
  zstep. zstep. zstep. zstep. zstep. zstep.
  release_frame FR ST (bv_unsigned sp + 48).
  zstep. zstep.
  assert (U48 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + 48)) = bv_unsigned sp + 48) by (apply unsigned_lit; lia).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut; [eapply HOFLADD with (lo := lo) (nx := wz 0);
                       [ unfold stdio_ok, A_LIBC, A_OFL_LOCK; refine (conj _ (conj _ _)); eassumption
                       | unfold ofl_empty, A_OFL_HEAD; eassumption | eassumption
                       | rewrite UH; exact LNK | rewrite UH; lia | rewrite UH; unfold A_LIBC, A_OFL_HEAD; lia
                       | rewrite UH; lia | unfold A_OFL_HEAD; lia | rewrite U48; eassumption
                       | rewrite U48; unfold OFL_ADD_K; lia ]
                    | unfold __ofl_add_post, OFL_ADD_K, ofl_one, stdio_ok, A_OFL_HEAD, A_LIBC, A_OFL_LOCK; post_call rsegs mm] end.
  match goal with H : stk _ _ lo (bv_unsigned (Z_to_bv 64 (bv_unsigned sp + 48))) |- _ => rewrite U48 in H; rename H into STF end.
  match goal with H : rw_cells _ _ (bv_unsigned (Z_to_bv 64 h) + 104) _ |- _ => rewrite UH in H; rename H into LNK2 end.
  match goal with H : rw_cells _ _ 613576 [C8 (wz (bv_unsigned (Z_to_bv 64 h)))] |- _ => rewrite UH in H; rename H into HEAD end.
  apply evt_done. do 15 eexists. split; [reflexivity|].
  split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [exact STF|].
  split.
  { exists (firstn 8 (skipn 272 junk)), (firstn 1024 (skipn 8 (skipn 272 junk))).
    split; [rewrite !firstn_length, !skipn_length, JL; reflexivity|].
    split; [rewrite !firstn_length, !skipn_length, JL; reflexivity|].
    apply mfw_split. split; [exact PRE|]. split; [exact LNK2 | exact POST]. }
  split; [unfold ofl_one, A_OFL_HEAD; exact HEAD|].
  unfold stdio_ok, A_LIBC, A_OFL_LOCK. refine (conj _ (conj _ _)); eassumption.
Qed.
