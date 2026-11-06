From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.Lib Require Import PropExec MState Mem Exec Frame Cells Step.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.Reloc Require Import RStep.
Import ListNotations.
Open Scope Z_scope.

Definition COPY_DEPTH : Z := 2240.
Definition SN_WRITE_DEPTH : Z := 64 + COPY_DEPTH.

Section Img.
Context {IMG : RImg}.
Variable copy_ready : (word -> option byte) -> Z -> Z -> Z -> Z -> Prop.

Definition memcpy_stack_post
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (a0 a1 a2 : word)
    (src : list byte) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom img_segs)
    /\ munch [(bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2);
              (bv_unsigned sp - COPY_DEPTH, bv_unsigned sp)] m m'
    /\ wmono img_segs m m' /\ mem_inv img_segs m'
    /\ stk img_segs m' (bv_unsigned sp - COPY_DEPTH) (bv_unsigned sp)
    /\ rw_cells img_segs m' (bv_unsigned a0) [CB (Z.to_nat (bv_unsigned a2)) src]
    /\ bytes_at img_segs m' (bv_unsigned a1) src.

Definition memcpy_stack_contract : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (src junk : list byte),
  bytes_at img_segs m (bv_unsigned a1) src -> length src = Z.to_nat (bv_unsigned a2) ->
  rw_cells img_segs m (bv_unsigned a0) [CB (Z.to_nat (bv_unsigned a2)) junk] ->
  (bv_unsigned a1 + bv_unsigned a2 <= bv_unsigned a0 \/ bv_unsigned a0 + bv_unsigned a2 <= bv_unsigned a1) ->
  (bv_unsigned a1 + bv_unsigned a2 <= bv_unsigned sp - COPY_DEPTH \/ bv_unsigned sp <= bv_unsigned a1) ->
  mem_inv img_segs m ->
  stk img_segs m (bv_unsigned sp - COPY_DEPTH) (bv_unsigned sp) ->
  copy_ready m (bv_unsigned sp) (bv_unsigned a0) (bv_unsigned a1) (bv_unsigned a2) ->
  evt img_segs (memcpy_stack_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 src m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 (sym 0x21334)) fc None m (seg_rom img_segs)).

Definition sn_write_footprint (sp f CK cs dn : Z) : list ivl :=
  [(sp - SN_WRITE_DEPTH, sp); (f + 40, f + 48); (f + 56, f + 64); (CK, CK + 16); (cs, cs + dn)].

Definition sn_write_ready (m : word -> option byte) (sp f CK cs dn WB pn S sn : Z) : Prop :=
  forall m' D P N,
    munch (sn_write_footprint sp f CK cs dn) m m' -> wmono img_segs m m' ->
    cs <= D -> 0 <= N -> D + N <= cs + dn ->
    (P = WB /\ N <= pn \/ P = S /\ N <= sn) ->
    copy_ready m' (sp - 64) D P N.

Lemma sn_write_ready_transport : forall m m' sp f CK cs dn WB pn S sn,
  sn_write_ready m sp f CK cs dn WB pn S sn ->
  munch (sn_write_footprint sp f CK cs dn) m m' -> wmono img_segs m m' ->
  sn_write_ready m' sp f CK cs dn WB pn S sn.
Proof.
  intros m m' sp f CK cs dn WB pn S sn READY MU WM m2 D P N MU2 WM2 HD HN HEND HS.
  eapply READY; [eapply munch_trans; eauto | eapply wmono_trans; eauto | exact HD | exact HN | exact HEND | exact HS].
Qed.

End Img.
