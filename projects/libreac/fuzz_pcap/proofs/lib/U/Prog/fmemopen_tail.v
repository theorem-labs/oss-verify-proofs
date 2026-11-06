From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import SymAddr.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Lib Require Import PropExec MState Mem Cells Exec Frame Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Prog Require Import StdioModel StdioKB memset_c __ofl_add_c fmemopen_pro.
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

Lemma fmemopen_tail : memset_contract -> __ofl_add_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo h b : Z) (Fc junk : list byte)
         (r4 r3 r2 r1 r0 R : word),
    a0 = wz h -> 0 < h -> h mod 16 = 0 ->
    s1 = wz b -> s2 = wz (Z.of_nat (length Fc)) -> s3 = wz (symaddr (Symbols.Ubsan.Sec.s_rodata + 0x6d)%Z) -> s4 = wz 0 ->
    bytes_at rsegs m b Fc -> 0 < b ->
    rw_cells rsegs m h [CB 1304 junk] ->
    rw_cells rsegs m (bv_unsigned sp) [C8 r4; C8 r3; C8 r2; C8 r1; C8 r0; C8 R] ->
    stk rsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp -> (symaddr ImgPages.Ubsan.top) <= lo -> bv_unsigned sp + 48 < 2 ^ 63 ->
    h + 1304 <= lo -> b + Z.of_nat (length Fc) <= lo ->
    (h + 1304 <= A_LIBC \/ A_OFL_HEAD + 8 <= h) -> (h + 1304 <= b \/ b + Z.of_nat (length Fc) <= h) ->
    (h + 1304 <= (symaddr (Symbols.Ubsan.Sec.s_rodata + 0x6d)%Z) \/ (symaddr (Symbols.Ubsan.Sec.s_rodata + 0x70)%Z) <= h) ->
    (b + Z.of_nat (length Fc) <= A_OFL_HEAD \/ A_OFL_HEAD + 8 <= b) ->
    stdio_ok m -> ofl_empty m -> mem_inv rsegs m ->
    evt rsegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
        ms' = MS (mkR R (Z_to_bv 64 (bv_unsigned sp + 48)) gp tp t0' t1' t2' r0 r1 (wz h) a1' a2' a3' a4' a5' a6' a7'
                      r2 r3 r4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc R) fc None m' (seg_rom rsegs)
        /\ munch [(bv_unsigned sp, bv_unsigned sp + 48); (h, h + 1304); (A_OFL_HEAD, A_OFL_HEAD + 8)] m m'
        /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp + 48)
        /\ mstl m' h b Fc 0 (wz 0) (wz 0) /\ ofl_one m' h /\ stdio_ok m')
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 (symaddr (Symbols.Ubsan.s_fmemopen + 0x9c)%Z)) fc None m (seg_rom rsegs)).
Proof.
  intros HMEMSET HOFLADD ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo h b Fc junk r4 r3 r2 r1 r0 R EA0 H0 H16 ES1 ES2 ES3 ES4 BF B0 BLK FR ST LS L5 S63 LH LB DL DB DM DBO HSO HE MI.
  subst a0 s1 s2 s3 s4.
  unfold memset_contract in HMEMSET. unfold __ofl_add_contract in HOFLADD.
  destruct HSO as [HT [HN HL]]. unfold ofl_empty in HE.
  unfold A_LIBC, A_OFL_LOCK, A_OFL_HEAD, wz in *.
  replace ((symaddr Symbols.Ubsan.s___libc) + 3) with (symaddr (Symbols.Ubsan.s___libc + 0x3)%Z) in HN by reflexivity.
  replace ((symaddr Symbols.Ubsan.s___libc) + 1) with (symaddr (Symbols.Ubsan.s___libc + 0x1)%Z) in HT by reflexivity.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  pose proof (bytes_at_bound _ _ _ _ BF) as BB.
  pose proof (rw_cells_bound _ _ _ _ BLK) as BH. cbn [cells_size csize] in BH.
  assert (JL : length junk = 1304%nat) by (destruct BLK as [[[HW _] _] _]; exact HW).
  pose proof (munch_refl [(bv_unsigned sp, bv_unsigned sp + 48); (h, h + 1304); ((symaddr Symbols.Ubsan.s_ofl_head), (symaddr Symbols.Ubsan.s_ofl_head) + 8)] m) as MU.
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
  match goal with H : mem_inv rsegs _ |- _ => pose proof (mode_bytes _ H) as BM0 end. cbn [MODE_STR app] in BM0.
  zstep. zstep.
  zstep. if_false.
  zstep. zstep. zstep. if_true.
  zstep. zstep.
  zstep. zstep. zstep. if_false.
  zstep. zstep. if_false.
  zstep. zstep.
  zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (RDT : ov_read_bytes rsegs mm (Z_to_bv 64 (symaddr (Symbols.Ubsan.s___libc + 0x1)%Z)) 1 = Some [Z_to_bv 8 0]) end.
  { change (Z_to_bv 64 (symaddr (Symbols.Ubsan.s___libc + 0x1)%Z)) with (wa ((symaddr (Symbols.Ubsan.s___libc + 0x1)%Z) + 0)).
    rewrite (bytes_at_read rsegs _ (symaddr (Symbols.Ubsan.s___libc + 0x1)%Z) [Z_to_bv 8 0] 0 1 HT ltac:(lia)) by (cbn; lia). reflexivity. }
  zstep.
  zstep. zstep. zstep. zstep.
  zstep. if_false.
  zstep. zstep.
  zstep.
  match goal with H : rw_cells _ _ h (C4 (Z_to_bv 64 8) :: _) |- _ => rename H into ZC end.
  replace (h + Z.of_nat (272 + 0)) with (h + 272) in BREST by lia.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
  assert (MF : rw_cells rsegs mm h (mfile_cells h b (Z.of_nat (length Fc)) (wz 8) (wz 0) (wz 0) (wz 0) (wz 0) (wz 0)
                 (wz 0) (wz 0) (wz 0) (wz 0) (firstn 8 (skipn 272 junk)) (firstn 1024 (skipn 8 (skipn 272 junk))))) end.
  { match type of ZC with rw_cells _ ?mm0 h ?cs0 =>
      assert (ZB : rw_cells rsegs mm0 h (cs0 ++ [CB 8 (firstn 8 (skipn 272 junk)); CB 1024 (firstn 1024 (skipn 8 (skipn 272 junk)))])) end.
    { apply rw_cells_app. split; [exact ZC|]. cbn [cells_size csize Nat.add].
      replace (h + Z.of_nat 272) with (h + 272) by lia. exact BREST. }
    eapply rw_cells_bytes_eq; [exact ZB | |].
    - cbn [cells_wf cell_wf mfile_cells]. rewrite !firstn_length, !skipn_length, JL. cbn. tauto.
    - assert (LE4M1 : le4 (Z_to_bv 64 (-1)) = le4 (wz 4294967295)).
      { unfold le4, wz. rewrite !Z_to_bv_unsigned.
        rewrite <- (Z_to_le_bytes_mod 4 (bv_wrap 64 (-1)) 32) by (cbn; lia).
        rewrite <- (Z_to_le_bytes_mod 4 (bv_wrap 64 4294967295) 32) by (cbn; lia).
        reflexivity. }
      cbn [cells_bytes cbytes mfile_cells app]. rewrite !LE4M1. reflexivity. }
  apply mfile_split in MF. destruct MF as (PRE & LNK & POST). unfold mf_pre in PRE. unfold mf_post in POST.
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
  let oh := constr:(symaddr Symbols.Ubsan.s_ofl_head) in
  match goal with H : rw_cells _ _ oh [C8 (wz (bv_unsigned (Z_to_bv 64 h)))] |- _ => rewrite UH in H; rename H into HEAD end.
  apply evt_done. do 15 eexists. split; [reflexivity|].
  split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [exact STF|].
  split.
  { unfold mstl. exists (wz 8), (wz 0), 0, None. split.
    - unfold mfile. exists (firstn 1024 (skipn 8 (skipn 272 junk))). split.
      + unfold mfile_raw. exists (wz 0), (wz 0), (wz 0), (firstn 8 (skipn 272 junk)). split.
        * apply mfile_split. cbn [rpos_of rend_of]. split; [exact PRE|]. split; [exact LNK2 | exact POST].
        * rewrite !firstn_length, !skipn_length, JL. cbn. split; [reflexivity|]. split; [reflexivity|]. split; lia.
      + split; [lia|]. split; [exact I|]. split; [eassumption|]. split; [lia|]. lia.
    - split; [left; reflexivity|]. split; [left; reflexivity|]. split; [cbn; lia|].
      intros E. apply (f_equal bv_unsigned) in E. vm_compute in E. discriminate E. }
  split; [unfold ofl_one, A_OFL_HEAD; exact HEAD|].
  unfold stdio_ok, A_LIBC, A_OFL_LOCK. refine (conj _ (conj _ _)); eassumption.
Qed.
