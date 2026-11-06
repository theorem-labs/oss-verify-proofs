From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import SymAddr.
From OSSVerify.libreac.fuzz_pcap Require Symbols.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Lib Require Import PropExec MState Mem Cells Exec Frame Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Spec Require Import StrFun StrFun2.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog Require Import StdioModel strchr_c.
Import ListNotations.
Open Scope Z_scope.

Definition MALLOC_FN : Z := Eval compute in Symbols.Plain.s_malloc.
Definition MODE_STR : list byte := [Z_to_bv 8 114; Z_to_bv 8 98].
Definition RWA_STR : list byte := [Z_to_bv 8 114; Z_to_bv 8 119; Z_to_bv 8 97].
Definition RWA_SLACK : list byte := [Z_to_bv 8 47; Z_to_bv 8 100; Z_to_bv 8 101; Z_to_bv 8 118; Z_to_bv 8 47; Z_to_bv 8 110].

Lemma mode_bytes : forall m, mem_inv rsegs m -> bytes_at rsegs m (symaddr (Symbols.Plain.Sec.s_rodata + 0x6d)%Z) (MODE_STR ++ Z_to_bv 8 0 :: []).
Proof.
  intros m MI. apply ro_bytes_at; [exact MI | lia | cbn; lia |].
  cbn [MODE_STR app ro_bytes]. unfold ro_byte. repeat split; vm_compute; reflexivity.
Qed.

Lemma rwa_bytes : forall m, mem_inv rsegs m -> bytes_at rsegs m (symaddr (Symbols.Plain.Sec.s_rodata + 0xf6)%Z) (RWA_STR ++ Z_to_bv 8 0 :: RWA_SLACK).
Proof.
  intros m MI. apply ro_bytes_at; [exact MI | lia | cbn; lia |].
  cbn [RWA_STR RWA_SLACK app ro_bytes]. unfold ro_byte. repeat split; vm_compute; reflexivity.
Qed.

Definition fmemopen_pro_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (a0 a1 a2 : word) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists sp' t0 t1 t2 a0' a1' a2' a3 a4 a5 a6 a7 s4' t3 t4 t5 t6 m1,
    ms' = MS (mkR (Z_to_bv 64 (symaddr (Symbols.Plain.s_fmemopen + 0x9c)%Z)) sp' gp tp t0 t1 t2 s0 a0 a0' a1' a2' a3 a4 a5 a6 a7 a1 a2 s4' s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 MALLOC_FN) fc None m1 (seg_rom rsegs)
    /\ bv_unsigned sp' = bv_unsigned sp - 48 /\ a0' = Z_to_bv 64 1304 /\ s4' = Z_to_bv 64 0
    /\ rw_cells rsegs m1 (bv_unsigned sp - 48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ munch [(bv_unsigned sp - 80, bv_unsigned sp)] m m1 /\ wmono rsegs m m1 /\ mem_inv rsegs m1
    /\ stk rsegs m1 lo (bv_unsigned sp - 48).

Lemma fmemopen_pro : strchr_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z),
    stk rsegs m lo (bv_unsigned sp) -> lo + 80 <= bv_unsigned sp -> (symaddr ImgPages.Plain.top) <= lo ->
    a2 = Z_to_bv 64 (symaddr (Symbols.Plain.Sec.s_rodata + 0x6d)%Z) -> bv_unsigned a0 <> 0 -> mem_inv rsegs m ->
    evt rsegs (fmemopen_pro_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 (symaddr Symbols.Plain.s_fmemopen)) fc None m (seg_rom rsegs)).
Proof.
  intros HSTRCHR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo ST LO HI EA2 A0 MI.
  subst a2. unfold strchr_contract in HSTRCHR.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  pose proof (zr_word a0) as Ra0. unfold inr64 in Ra0.
  pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  assert (L0 : 0 <= lo) by (destruct ST as [? _]; lia).
  carve_frame 48%nat ST.
  zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
  assert (U48 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -48)) = bv_unsigned sp + -48) by (apply unsigned_lit; lia).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut; [eapply HSTRCHR with (lo := lo) (str := MODE_STR) (slack := []);
                       [ rewrite U48; eassumption | rewrite unsigned_lit by lia; apply mode_bytes; eassumption
                       | cbv; intros [H|[H|H]]; discriminate H || exact H
                       | rewrite unsigned_lit by lia; cbn; lia | eassumption
                       | rewrite U48; lia | rewrite U48, unsigned_lit by lia; cbn; lia ]
                    | unfold strchr_post; post_call rsegs mm] end.
  replace (Z_to_bv 64 (strchr_val (bv_unsigned (Z_to_bv 64 (symaddr (Symbols.Plain.Sec.s_rodata + 0x6d)%Z))) (bv_unsigned (Z_to_bv 64 43) mod 256) MODE_STR))
    with (Z_to_bv 64 0) by (vm_compute; reflexivity).
  match goal with H : stk _ _ lo (bv_unsigned (Z_to_bv 64 _)) |- _ => rewrite U48 in H; rename H into ST end.
  match goal with H : mem_inv rsegs _ |- _ => pose proof (mode_bytes _ H) as BM end. cbn [MODE_STR app] in BM.
  zstep. zstep. zstep. zstep. zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut; [eapply HSTRCHR with (lo := lo) (str := RWA_STR) (slack := RWA_SLACK);
                       [ rewrite U48; eassumption | rewrite unsigned_lit by lia; apply rwa_bytes; eassumption
                       | cbv; intros [H|[H|[H|H]]]; discriminate H || exact H
                       | rewrite unsigned_lit by lia; cbn; lia | eassumption
                       | rewrite U48; lia | rewrite U48, unsigned_lit by lia; cbn; lia ]
                    | unfold strchr_post; post_call rsegs mm] end.
  match goal with H : stk _ _ lo (bv_unsigned (Z_to_bv 64 _)) |- _ => rewrite U48 in H; rename H into ST2 end.
  replace (Z_to_bv 64 (strchr_val (bv_unsigned (Z_to_bv 64 (symaddr (Symbols.Plain.Sec.s_rodata + 0xf6)%Z))) (bv_unsigned (Z_to_bv 64 114) mod 256) RWA_STR))
    with (Z_to_bv 64 (symaddr (Symbols.Plain.Sec.s_rodata + 0xf6)%Z)) by (vm_compute; reflexivity).
  zstep. if_false. zstep. if_true. zstep. if_false. zstep. zstep.
  apply evt_done. unfold fmemopen_pro_post.
  replace (bv_unsigned sp - 48) with (bv_unsigned sp + -48) by lia.
  do 18 eexists. split; [reflexivity|].
  split; [exact U48|]. split; [reflexivity|]. split; [reflexivity|].
  refine (conj _ (conj _ (conj _ (conj _ _)))); eassumption.
Qed.
