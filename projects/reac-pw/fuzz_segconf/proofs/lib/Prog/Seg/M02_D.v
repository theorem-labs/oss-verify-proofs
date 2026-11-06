(* Segment M02 of reac-pw/fuzz_segconf LLVMFuzzerTestOneInput (plain, ELF 8dec0b814e6f), piece D: 0x13c64 .. the
   `jal calloc` at 0x13c98, M02D.M02_D_stmt.
   Code: a1 = 0x10540 (seg_spec.STR_NOSUCH, "nosuch0" in .rodata), a2 = 7, a0 = s0 = m, `jal m_find` (0x13c74; its
   premise: m's block, the 7 image bytes, which lie below lo = S - 65536 >= 0x60000, and the stack [S - 65536, S - 208)
   by M02K.m02_stack_ok); `bnez a0` to 0x13c8c: m_find_ptr is 0 exactly when SegModel.m_find mc S_nosuch = None
   (else it is m + 256 i with i < m->n <= 32, nonzero). On None: a1 = 0x10540, a0 = s8 = c, `jal check_absent`
   (0x13c88; query_pre with the C string S_nosuch at 0x10540, and absent rc S_nosuch = probe_ok rc mc S_nosuch, the
   sixth check of M02_model, since m_find misses it). 0x13c8c: s4 = s6 + 1 = cap + 1, a1 = 18, a0 = s4,
   `jal calloc` (0x13c98 + 0x2c6c = M02_CALLOC, ra = M02_RA). The memory stays an M02_inv successor of m0 across both
   calls (M02K.m02_inv_step: each callee writes only its frame below main's sp).
   The rodata bytes are read as check_knock_refused.v's ckr_tnp_at (ro_bytes_b by vm_compute, ro_bytes_b_sound,
   ro_bytes_at with mem_inv). [MdPure] holds the lemmas that do not mention the image; m_find's index bound is
   M02Bridge.mb_mfind_lt.
   Part of the proof of LLVMFuzzerTestOneInput: piece D of segment M02 of its walk; no released proof of
   fuzz_segconf's LLVMFuzzerTestOneInput exists, written new (segment walk piece). *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import Tac ZBridge FP.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib Require MemNorm.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec seg_spec
  reac_segconf_find_c reac_segconf_role_c m_find_c check_absent_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog.Seg Require Import M02D M02K.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog.Seg Require M02_bridge.
Import ListNotations.
Open Scope Z_scope.

Module MdPure.

Lemma md_nf_dec : forall l, forallb (fun x => negb (x =? 0)) l = true -> ~ In 0 l.
Proof.
  induction l as [|a l IH]; intros H Hin; [exact Hin|].
  cbn [forallb] in H. apply andb_prop in H as [H1 H2]. cbn [In] in Hin.
  destruct Hin as [E|Hin]; [subst a; cbn in H1; discriminate H1 | exact (IH H2 Hin)].
Qed.

(** check_absent's premise for "nosuch0" when m_find misses it: the sixth check of M02_model. *)
Lemma md_absent : forall rc mc, probe_ok rc mc S_nosuch = true -> m_find mc S_nosuch = None ->
  absent rc S_nosuch = true.
Proof. intros rc mc H E. unfold probe_ok in H. rewrite E in H. exact H. Qed.

Lemma md_ns_slen : length S_nosuch = 7%nat.
Proof. reflexivity. Qed.

Lemma md_ns_nf : ~ In 0 S_nosuch.
Proof. apply md_nf_dec. vm_compute. reflexivity. Qed.

End MdPure.

Import MdPure.

(** ** "nosuch0" at STR_NOSUCH in the image *)
Definition NS_B : list byte := zb S_nosuch.

Lemma md_ns_ro : ro_bytes_b rsegs STR_NOSUCH (NS_B ++ [ZERO]) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma md_ns_len : length NS_B = 7%nat.
Proof. reflexivity. Qed.
Lemma md_ns_zs : zs NS_B = S_nosuch.
Proof. vm_compute. reflexivity. Qed.

Lemma md_ns_at : forall m, mem_inv rsegs m -> bytes_at rsegs m STR_NOSUCH (NS_B ++ [ZERO]).
Proof.
  intros m MI. apply (ro_bytes_at rsegs m);
    [exact MI | unfold STR_NOSUCH; lia | rewrite length_app, md_ns_len; cbn [length]; unfold STR_NOSUCH; lia |].
  exact (ro_bytes_b_sound rsegs _ STR_NOSUCH md_ns_ro).
Qed.

(** A branch whose other side the context refutes. *)
Ltac md_if := lazymatch goal with
  | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) =>
      let K := fresh "K" in if_cases K;
      [ first [ exfalso; zify_cond K; rewrite ?unsigned_lit_wrap in K; lia | clear K ]
      | first [ exfalso; zify_cond K; rewrite ?unsigned_lit_wrap in K; lia | clear K ] ]
  | _ => idtac end.

(** ** The walk *)
Theorem m02_D : m_find_contract -> check_absent_contract -> M02_D_stmt.
Proof.
  intros MF CA. unfold M02_D_stmt.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m0 m
    S c mm cap rc mc ret Esp Es0 Es8 Es10 Es6 HFC HMOD HM HI.
  subst sp s0 s8 s10 s6.
  pose proof HMOD as (_ & _ & _ & _ & _ & HNS).
  pose proof HM as BN. eapply m02_bnds in BN.
  destruct BN as (H16 & HT & H47 & Hc0 & Hc16 & Hc & Hm0 & Hm16 & Hm).
  unfold SEG_C_SIZE in Hc. unfold SEG_M_SIZE in Hm.
  assert (HF : M02_FRAME = 208) by reflexivity.
  (* 0x13c8c .. 0x13c98: s4 = cap + 1, a1 = 18, a0 = s4, `jal calloc` *)
  assert (TAIL : forall (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word)
                        (m' : word -> option byte),
    M02_inv S m0 m' ->
    evt rsegs (M02_post S c mm cap gp tp m0)
      (MS (mkR x1 (Z_to_bv 64 (S - M02_FRAME)) gp tp x5 x6 x7 (Z_to_bv 64 mm) s1 x10 x11 x12 x13 x14 x15 x16 x17
               s2 s3 s4 s5 (Z_to_bv 64 cap) s7 (Z_to_bv 64 c) s9 (Z_to_bv 64 (mm + MC_N)) s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x13c8c) fc None m' (seg_rom rsegs))).
  { intros x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m' HI'.
    do 4 zstep.
    rewrite ?Z.add_0_r.
    apply evt_done. unfold M02_post.
    do 23 eexists. split; [reflexivity|]. split; [exact HFC | exact HI']. }
  assert (MI0 : mem_inv rsegs m) by (eapply m02_mem_inv; eassumption).
  assert (MC0 : mconf_at rsegs m mm mc) by (eapply m02_mconf; eassumption).
  assert (ST48 : stack_ok rsegs m (S - 65536) (S - M02_FRAME) M_FIND_STACK)
    by (eapply m02_stack_ok; try eassumption; unfold M_FIND_STACK; lia).
  pose proof (proj1 (proj1 (bytes_at_app rsegs m STR_NOSUCH NS_B [ZERO]) (md_ns_at m MI0))) as NS7.
  pose proof (M02_bridge.M02Bridge.mb_mconf_n rsegs m mm mc MC0) as (_ & L32).
  (* 0x13c64 auipc a0; 0x13c68 addi a1 (= 0x10540); 0x13c6c li a2,7; 0x13c70 mv a0,s0; 0x13c74 jal m_find *)
  do 5 zstep.
  eapply evt_cut.
  { eapply MF with (lo := S - 65536) (mc := mc) (l := NS_B).
    unfold m_find_pre. rewrite ?unsigned_lit by lia. rewrite ?Z.add_0_r.
    split; [lia|]. split; [exact Hm16|]. split; [exact MC0|].
    split; [unfold apart, SEG_M_SIZE; left; lia|].
    split; [exact NS7|]. split; [rewrite md_ns_len; reflexivity|].
    split; [unfold apart; left; lia|].
    split; [exact ST48 | exact MI0]. }
  intros ms1 (u0 & u1 & u2 & ua1 & ua2 & ua3 & ua4 & ua5 & ua6 & ua7 & u3 & u4 & u5 & u6 & m1 & -> &
              MU1 & WM1 & MI1 & _ & _).
  rewrite ret_pc_even by (try lia; reflexivity).
  rewrite !unsigned_lit in MU1 by lia.
  assert (HI1 : M02_inv S m0 m1).
  { apply (m02_inv_step S m0 m m1 _ HI MU1 WM1 MI1); unfold M_FIND_STACK; [m02_subfp | m02_low]. }
  rewrite ?unsigned_lit by lia. rewrite ?Z.add_0_r. rewrite md_ns_zs.
  unfold m_find_ptr.
  destruct (m_find mc S_nosuch) as [i|] eqn:EF.
  - (* found: a0 = m + 256 i <> 0, `bnez` taken to 0x13c8c *)
    pose proof (M02_bridge.M02Bridge.mb_mfind_lt mc S_nosuch i EF) as Hi.
    assert (RP : 0 < mseg_addr mm i < 2 ^ 64) by (unfold mseg_addr, MSEG_SIZE; lia).
    revert RP. generalize (mseg_addr mm i). intros p RP.
    zstep. md_if.
    eapply TAIL. exact HI1.
  - (* missed: a0 = 0, `bnez` falls through to check_absent(c, "nosuch0") *)
    pose proof (md_absent rc mc HNS EF) as AB.
    zstep. md_if.
    (* 0x13c7c auipc a0; 0x13c80 addi a1 (= 0x10540); 0x13c84 mv a0,s8; 0x13c88 jal check_absent *)
    do 4 zstep.
    assert (R1 : rconf_at rsegs m1 c rc) by (eapply m02_rconf; eassumption).
    assert (ST80 : stack_ok rsegs m1 (S - 65536) (S - M02_FRAME) CHECK_ABSENT_STACK)
      by (eapply m02_stack_ok; try eassumption; unfold CHECK_ABSENT_STACK, ROLE_STACK, FIND_STACK; lia).
    pose proof (md_ns_at m1 MI1) as NSZ.
    eapply evt_cut.
    { eapply CA with (lo := S - 65536) (rc := rc) (nm := S_nosuch).
      unfold check_absent_pre, query_pre. rewrite ?unsigned_lit by lia. rewrite ?Z.add_0_r.
      split; [|exact AB].
      split; [lia|]. split; [exact Hc16|]. split; [exact R1|].
      split; [unfold apart, SEG_C_SIZE; left; lia|].
      split; [lia|]. split; [exists NS_B; split; [exact NSZ | split; [exact md_ns_zs | exact md_ns_nf]]|].
      split; [unfold apart; rewrite md_ns_slen; left; lia|].
      split; [exact ST80 | exact MI1]. }
    intros ms2 (v0 & v1 & v2 & va0 & va1 & va2 & va3 & va4 & va5 & va6 & va7 & v3 & v4 & v5 & v6 & m2 & -> &
                MU2 & WM2 & MI2 & _ & _).
    rewrite ret_pc_even by (try lia; reflexivity).
    rewrite !unsigned_lit in MU2 by lia.
    assert (HI2 : M02_inv S m0 m2).
    { apply (m02_inv_step S m0 m1 m2 _ HI1 MU2 WM2 MI2); unfold CHECK_ABSENT_STACK, ROLE_STACK, FIND_STACK;
        [m02_subfp | m02_low]. }
    eapply TAIL. exact HI2.
Qed.
