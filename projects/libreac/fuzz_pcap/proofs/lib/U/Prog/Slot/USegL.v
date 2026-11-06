From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import SymAddr.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Lib Require Import PropExec MState Mem Cells Exec Frame Step Tac Bytes ZBridge Arr.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Spec Require Import StrFun.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Prog Require Import StdioModel pcap_source_next_lib rd_u32_c rd32f_c bcmp_c.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog Require Import pcap_source_struct pcap_source_struct_next.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog.Slot Require Import PWalkDef PWalk.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Prog.Slot Require Import USegLs.
Import ListNotations.
Open Scope Z_scope.

(* The record loop of the ubsan entry function (0x12e04-0x1304c, fuzz/fuzz_pcap.c:132-216): segment D (after the
   first pcap_source_next call), segment L (one turn of the loop, up to the next pcap_source_next call; its skip loop
   0x12e78-0x12eb8 is ubs_L_skip in USegLs.v) and segment L2 (after each later call). *)

Ltac addr_eq_tac ::= first [ apply wa_of_var; lia
                           | symmetry; first [ apply wa_of_Z_to_bv; lia | apply wa_of_var; lia | unfold wa; f_equal; lia ] ].

(* Answers of pcap_source_next are signed: -1 <= n < 2^26. *)
Lemma ul_lts0_wz : forall n, -1 <= n < 2 ^ 26 -> bv_lts (Z_to_bv 64 0) (Z_to_bv 64 n) = (0 <? n).
Proof.
  intros n Hn. unfold bv_lts. rewrite !zb_signed. rewrite unsigned_lit by lia. rewrite unsigned_lit_wrap.
  destruct (Z.ltb_spec n 0) as [N|N].
  - assert (n = -1) by lia. subst n. reflexivity.
  - rewrite Z.mod_small by lia. destruct (Z.ltb_spec n (2 ^ 63)); [|lia]. cbn. reflexivity.
Qed.

(* D: 0x12e04 (a0 = n0) to K4 0x12e38 (n0 > 0, loop index 0) or K5 0x1304c (n0 <= 0). *)
Lemma ubs_D_x : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                         t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
                         (lo sp_h n0 b buf : Z) (v8 v16 v32 : word),
  bv_unsigned sp = sp_h -> a0 = wz n0 -> -1 <= n0 < 2 ^ 26 -> s0 = wz b -> s2 = wz buf ->
  rw_cells rsegs m (sp_h + 8) [C8 v8] -> rw_cells rsegs m (sp_h + 16) [C8 v16] -> rw_cells rsegs m (sp_h + 32) [C8 v32] ->
  mem_inv rsegs m -> stk rsegs m lo (sp_h + 176) ->
  evt rsegs
    (fun ms' =>
       (0 < n0 /\
        exists m' : word -> option byte,
          ms' = MS (mkR ra sp gp tp t0 t1 t2 (wz b) s1 (wz n0) (wz (1000000 * 2 ^ 32)) a2 (wz 0) a4 a5 a6 a7 (wz (-8)) s3
                        (bv_not (wz b)) (wz n0) s6 s7 s8 (wz 24) s10 (wz n0) t3 t4 t5 t6)
                   F (Z_to_bv 64 (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0x1ec)%Z)) fc None m' (seg_rom rsegs) /\
          munch [(sp_h + 8, sp_h + 24); (sp_h + 32, sp_h + 40)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
          stk rsegs m' lo (sp_h + 176) /\
          rw_cells rsegs m' (sp_h + 8) [C8 (wz (buf + 12))] /\
          rw_cells rsegs m' (sp_h + 16) [C8 (wz (1000000 * 2 ^ 32))] /\
          rw_cells rsegs m' (sp_h + 32) [C8 (wz 0)]) \/
       (n0 <= 0 /\
        ms' = MS (mkR ra sp gp tp t0 t1 t2 (wz b) s1 (wz n0) a1 a2 a3 a4 a5 a6 a7 (wz buf) s3 s4 (wz n0) s6 s7 s8 (wz 24)
                      s10 (wz n0) t3 t4 t5 t6) F (Z_to_bv 64 (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0x400)%Z)) fc None m (seg_rom rsegs)))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0x1b8)%Z)) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo sp_h n0 b buf v8 v16 v32 HSP E0 Hn E8 E2 H8 H16 H32 MI ST.
  subst sp_h a0 s0 s2. unfold wz in *.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  step. step.
  rewrite ul_lts0_wz by lia.
  destruct (Z.ltb_spec 0 n0) as [P|P]; cbn [negb]; cbv iota.
  - pose proof (munch_refl [(bv_unsigned sp + 8, bv_unsigned sp + 24); (bv_unsigned sp + 32, bv_unsigned sp + 40)] m) as MU.
    pose proof (wmono_refl rsegs m) as WM.
    do 11 step.
    rewrite ul_not_word.
    let mm := cur_mem in
    apply evt_done; left; split; [exact P|]; exists mm.
    split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
    split; [exact H8|]. split; [exact H16|]. exact H32.
  - do 2 step.
    apply evt_done. right. split; [exact P | reflexivity].
Qed.

(* L2: 0x13034 (a0 = n', the answer of a later call) to K4 0x12e38 (n' > 0) or K5 0x1304c (n' <= 0). *)
Lemma ubs_L2_x : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                          t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (n' first : Z),
  a0 = wz n' -> -1 <= n' < 2 ^ 26 -> s11 = wz first ->
  evt rsegs
    (fun ms' =>
       (0 < n' /\
        ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz n') a1 a2 (wz first) a4 a5 a6 a7 s2 s3 s4 (wz n') s6 s7 s8 s9
                      s10 (wz first) t3 t4 t5 t6) F (Z_to_bv 64 (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0x1ec)%Z)) fc None m (seg_rom rsegs)) \/
       (n' <= 0 /\
        ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz n') a1 a2 (wz first) a4 a5 a6 a7 s2 s3 s4 (wz n') s6 s7 s8 s9
                      s10 (wz first) t3 t4 t5 t6) F (Z_to_bv 64 (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0x400)%Z)) fc None m (seg_rom rsegs)))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0x3e8)%Z)) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m n' first E0 Hn E11.
  subst a0 s11. unfold wz in *.
  do 3 step.
  rewrite ul_lts0_wz by lia.
  destruct (Z.ltb_spec 0 n') as [P|P]; cbv iota.
  - apply evt_done. left. split; [exact P | reflexivity].
  - step. apply evt_done. right. split; [exact P | reflexivity].
Qed.

(* The end state of L, at the pcap_source_next call (0x13030 -> 0x13318): the return address 0x13034, the arguments
   (&ps, buf, cap, &ts), the next position Qn in s9, the loop index cell (sp_h + 32) and ts = -1 (sp_h + 40). *)
Definition QL (sp gp tp s0 s1 s2 s4 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : word -> option byte)
    (lo sp_h buf cap Qn : Z) (v32 : word) (ms' : machine_state) : Prop :=
  exists (t0' t1' t2' a4' a5' a6' a7' s3' s5' s6' s7' s8' t3' t4' t5' t6' : word) (m' : word -> option byte),
    ms' = MS (mkR (wz (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0x3e8)%Z)) sp gp tp t0' t1' t2' s0 s1 (wz (sp_h + 48)) (wz buf) (wz cap) (wz (sp_h + 40))
                  a4' a5' a6' a7' s2 s3' s4 s5' s6' s7' s8' (wz Qn) s10 s11 t3' t4' t5' t6')
             F (Z_to_bv 64 (symaddr Symbols.Ubsan.s_pcap_source_next)) fc None m' (seg_rom rsegs) /\
    munch [(sp_h + 32, sp_h + 48)] m0 m' /\ wmono rsegs m0 m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (sp_h + 176) /\
    rw_cells rsegs m' (sp_h + 32) [C8 v32] /\ rw_cells rsegs m' (sp_h + 40) [C8 (wz (-1))].

(* The common tail of the loop body, 0x12fc4-0x13030 (fuzz/fuzz_pcap.c:211-216 and the call at 132): the timestamp
   check through check_1 and mulhu, ts = -1, the new position, the arguments of the next pcap_source_next call.
   m0 is the memory at the start of L; m0 to m is the part of L before. *)
Lemma ul_L_ts : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                         t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m0 m : word -> option byte)
                         (Fc : list byte) (sw : bool) (lo sp_h b buf cap swz Q : Z) (v32 : word),
  rd32f_contract ->
  bv_unsigned sp = sp_h -> s7 = wz (b + Q) -> s6 = wz (bv_swrap 32 (incl sw Fc Q)) -> s9 = wz Q -> s1 = wz cap ->
  0 <= Q -> kind sw Fc cap Q = KFit -> 0 <= cap <= 2040 ->
  b <> 0 -> b + Z.of_nat (length Fc) < 2 ^ 63 -> bytes_at rsegs m b Fc ->
  bytes_at rsegs m (sp_h + 16) (le8 (wz (1000000 * 2 ^ 32))) -> bytes_at rsegs m (sp_h + 24) (le8 (wz buf)) ->
  rw_cells rsegs m (sp_h + 32) [C8 v32] -> rw_cells rsegs m (sp_h + 40) [C8 (wz (rec_ts sw Fc Q))] ->
  bytes_at rsegs m (sp_h + 56) (le4 (wz swz)) -> (swz = 0 \/ swz = 1) -> sw = (swz =? 1) ->
  munch [(sp_h + 32, sp_h + 48)] m0 m -> wmono rsegs m0 m -> mem_inv rsegs m -> stk rsegs m lo (sp_h + 176) ->
  evt rsegs (QL sp gp tp s0 s1 s2 s4 s10 s11 F fc m0 lo sp_h buf cap (Q + 16 + incl sw Fc Q) v32)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0x378)%Z)) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m0 m Fc sw lo sp_h b buf cap swz Q v32 RD HSP E7 E6 E9 E1 HQ KQ HC Hb HBN HB H16 H24 H32 H40 H56 HSW ESW
    MU0 WM0 MI ST.
  subst sp_h s7 s6 s9 s1. unfold wz in *.
  pose proof (bytes_at_bound rsegs _ _ _ HB) as BB.
  pose proof (kind_fit _ _ _ _ KQ) as (_ & _ & _ & HQL & KQ2). unfold flen in HQL.
  pose proof (pw_hw_range sw Fc Q 0) as R0. pose proof (pw_hw_range sw Fc Q 4) as R4.
  pose proof (incl_nonneg sw Fc Q) as R8.
  assert (RTS : 0 <= rec_ts sw Fc Q < 2 ^ 63) by (unfold rec_ts; lia).
  pose proof (ul_ro _ _ (C8 (Z_to_bv 64 (1000000 * 2 ^ 32))) H16 I) as R16.
  pose proof (ul_ro _ _ (C8 (Z_to_bv 64 buf)) H24 I) as R24.
  pose proof (ul_ro _ _ (C4 (Z_to_bv 64 swz)) H56 I) as R56.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  pose proof ST as (Lo0 & Hi64 & _).
  do 4 step.
  eapply evt_cut;
    [ eapply (ul_rd32 RD) with (Fc := Fc) (b := b) (swz := swz) (q := Q) (j := 0);
      first [ assumption | (apply ul_sx32_01; assumption) | reflexivity | (f_equal; lia) | lia ]
    | rd_post ].
  rewrite <- ESW.
  step. step. ifc false.
  do 3 step.
  rep_reg 10 (Z_to_bv 64 (hw sw Fc Q 0 * 2 ^ 32)) ltac:(apply ul_sh32; exact R0).
  do 2 step.
  rep_reg 21 (Z_to_bv 64 (hw sw Fc Q 0 * 1000000))
    ltac:(f_equal; unwrap; rewrite Z.shiftr_div_pow2 by lia; apply Z.div_unique_exact; lia).
  do 2 step.
  eapply evt_cut;
    [ eapply (ul_rd32 RD) with (Fc := Fc) (b := b) (swz := swz) (q := Q) (j := 4);
      first [ assumption | (apply ul_sx32_01; assumption) | reflexivity | (f_equal; lia) | lia ]
    | rd_post ].
  rewrite <- ESW.
  do 2 step. rewrite zx32_val, uns_swrap_mod32_0 by lia.
  step.
  rep_reg 10 (Z_to_bv 64 (rec_ts sw Fc Q)) ltac:(unfold rec_ts; f_equal; unwrap; lia).
  step. ifc false.
  do 2 step.
  do 3 step.
  rep_reg 10 (Z_to_bv 64 (incl sw Fc Q + 16)) ltac:(zx_eq).
  step.
  rep_reg 25 (Z_to_bv 64 (Q + 16 + incl sw Fc Q)) ltac:(f_equal; unwrap; lia).
  do 5 step.
  let mm := cur_mem in apply evt_done; unfold QL; do 16 eexists; exists mm.
  split; [reflexivity|]. split; [exact MU0|]. split; [exact WM0|]. split; [exact MI|]. split; [exact ST|].
  split; [exact H32|]. exact H40.
Qed.

(* An untagged record, 0x12fac-0x12fc0 (fuzz/fuzz_pcap.c:202-203): the answer is incl and the buffer holds the
   record's bytes (bcmp = 0); then the common tail. *)
Lemma ul_L_unt : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                          t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m0 m : word -> option byte)
                          (Fc : list byte) (sw : bool) (lo sp_h b buf cap swz Q : Z) (v32 : word),
  rd32f_contract -> bcmp_contract ->
  bv_unsigned sp = sp_h -> s3 = wz (incl sw Fc Q) -> s5 = wz (rec_len sw Fc Q) ->
  s6 = wz (bv_swrap 32 (incl sw Fc Q)) -> s7 = wz (b + Q) -> s8 = wz (b + Q + 16) -> s9 = wz Q -> s1 = wz cap ->
  tagged sw Fc Q = false -> 0 <= Q -> kind sw Fc cap Q = KFit -> 0 <= cap <= 2040 ->
  b <> 0 -> b + Z.of_nat (length Fc) < 2 ^ 63 -> bytes_at rsegs m b Fc ->
  bytes_at rsegs m (sp_h + 16) (le8 (wz (1000000 * 2 ^ 32))) -> bytes_at rsegs m (sp_h + 24) (le8 (wz buf)) ->
  rw_cells rsegs m (sp_h + 32) [C8 v32] -> rw_cells rsegs m (sp_h + 40) [C8 (wz (rec_ts sw Fc Q))] ->
  bytes_at rsegs m (sp_h + 56) (le4 (wz swz)) -> (swz = 0 \/ swz = 1) -> sw = (swz =? 1) ->
  bytes_at rsegs m buf (rec_bytes sw Fc Q) -> 4096 <= buf -> buf + 2040 < 2 ^ 63 ->
  munch [(sp_h + 32, sp_h + 48)] m0 m -> wmono rsegs m0 m -> mem_inv rsegs m -> stk rsegs m lo (sp_h + 176) ->
  evt rsegs (QL sp gp tp s0 s1 s2 s4 s10 s11 F fc m0 lo sp_h buf cap (Q + 16 + incl sw Fc Q) v32)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0x360)%Z)) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m0 m Fc sw lo sp_h b buf cap swz Q v32 RD BC HSP E3 E5 E6 E7 E8 E9 E1 TG HQ KQ HC Hb HBN HB H16 H24 H32
    H40 H56 HSW ESW HBUF Hbuf Hbuf2 MU0 WM0 MI ST.
  subst sp_h s3 s5 s6 s7 s8 s9 s1. unfold wz in *.
  pose proof (bytes_at_bound rsegs _ _ _ HB) as BB.
  pose proof (kind_fit _ _ _ _ KQ) as (_ & KR & _ & KQ1 & KQ2). unfold flen in KQ1.
  assert (RLI : rec_len sw Fc Q = incl sw Fc Q) by (unfold rec_len; rewrite TG; reflexivity).
  rewrite RLI.
  pose proof (ul_rec_raw_len sw Fc Q HQ KQ1) as LRAW.
  rewrite (ul_rb_untag sw Fc Q TG) in HBUF.
  pose proof (ul_bytes_sub m b Fc (Z.to_nat (Q + 16)) (Z.to_nat (incl sw Fc Q)) (b + Q + 16) HB ltac:(lia) ltac:(lia))
    as HRAW.
  change (firstn (Z.to_nat (incl sw Fc Q)) (skipn (Z.to_nat (Q + 16)) Fc)) with (rec_raw sw Fc Q) in HRAW.
  pose proof (ul_ro _ _ (C8 (Z_to_bv 64 buf)) H24 I) as R24.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  pose proof ST as (Lo0 & Hi64 & _).
  step. ifc false.
  do 4 step.
  eapply evt_cut; [eapply BC | ].
  { unwrap. exact HBUF. }
  { unwrap. exact HRAW. }
  { unwrap. apply ul_mcm_firstn; [lia | lia | reflexivity]. }
  { exact MI. }
  post_call rsegs m.
  step. ifc false.
  eapply ul_L_ts; first [ eassumption | reflexivity | (f_equal; lia) | lia ].
Qed.

(* The record checks 0x12ebc-0x1302c (fuzz/fuzz_pcap.c:162-216) from the record Q the skip loop stops at. *)
Lemma ul_L_rec : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                          t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m0 m : word -> option byte)
                          (Fc : list byte) (sw : bool) (lo sp_h b buf cap swz Q : Z) (v32 : word),
  rd32f_contract -> bcmp_contract ->
  bv_unsigned sp = sp_h -> s3 = wz (incl sw Fc Q) -> s6 = wz (bv_swrap 32 (incl sw Fc Q)) -> s7 = wz (b + Q) ->
  s8 = wz (Q + 16) -> s9 = wz Q -> s1 = wz cap -> s5 = wz (rec_len sw Fc Q) -> s10 = wz (symaddr Symbols.Ubsan.s_g_file_len) ->
  0 <= Q -> kind sw Fc cap Q = KFit -> 0 <= cap <= 2040 ->
  Z.of_nat (length Fc) < 2 ^ 26 -> b <> 0 -> b + Z.of_nat (length Fc) < 2 ^ 63 ->
  bytes_at rsegs m b Fc -> bytes_at rsegs m (symaddr Symbols.Ubsan.s_g_file_len) (le8 (wz (Z.of_nat (length Fc)))) ->
  bytes_at rsegs m (sp_h + 8) (le8 (wz (buf + 12))) -> bytes_at rsegs m (sp_h + 16) (le8 (wz (1000000 * 2 ^ 32))) ->
  bytes_at rsegs m (sp_h + 24) (le8 (wz buf)) ->
  rw_cells rsegs m (sp_h + 32) [C8 v32] -> rw_cells rsegs m (sp_h + 40) [C8 (wz (rec_ts sw Fc Q))] ->
  bytes_at rsegs m (sp_h + 56) (le4 (wz swz)) -> (swz = 0 \/ swz = 1) -> sw = (swz =? 1) ->
  bytes_at rsegs m (sp_h + 60) (le4 (wz (orig sw Fc Q))) ->
  bytes_at rsegs m (sp_h + 64) (le4 (wz (if tagged sw Fc Q then 1 else 0))) ->
  bytes_at rsegs m (sp_h + 68) (le2 (wz (if tagged sw Fc Q then rec_vid Fc Q else 0))) ->
  bytes_at rsegs m buf (rec_bytes sw Fc Q) -> 4096 <= buf -> buf + 2040 < 2 ^ 63 ->
  munch [(sp_h + 32, sp_h + 48)] m0 m -> wmono rsegs m0 m -> mem_inv rsegs m -> stk rsegs m lo (sp_h + 176) ->
  evt rsegs (QL sp gp tp s0 s1 s2 s4 s10 s11 F fc m0 lo sp_h buf cap (Q + 16 + incl sw Fc Q) v32)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0x270)%Z)) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m0 m Fc sw lo sp_h b buf cap swz Q v32 RD BC HSP E3 E6 E7 E8 E9 E1 E5 E10 HQ KQ HC HN Hb HBN HB HBL H8 H16
    H24 H32 H40 H56 HSW ESW H60 H64 H68 HBUF Hbuf Hbuf2 MU0 WM0 MI ST.
  subst sp_h s3 s6 s7 s8 s9 s1 s5 s10. unfold wz in *.
  pose proof (bytes_at_bound rsegs _ _ _ HB) as BB.
  pose proof (kind_fit _ _ _ _ KQ) as (_ & KR & _ & KQ1 & KQ2). unfold flen in KQ1.
  pose proof (pw_hw_range sw Fc Q 12) as R12. change (hw sw Fc Q 12) with (orig sw Fc Q) in R12.
  pose proof (ul_ro _ _ (C8 (Z_to_bv 64 (Z.of_nat (length Fc)))) HBL I) as RL.
  pose proof (ul_ro _ _ (C8 (Z_to_bv 64 (buf + 12))) H8 I) as R8.
  pose proof (ul_ro _ _ (C8 (Z_to_bv 64 buf)) H24 I) as R24.
  pose proof (ul_ro _ _ (C4 (Z_to_bv 64 swz)) H56 I) as R56.
  pose proof (ul_ro _ _ (C4 (Z_to_bv 64 (orig sw Fc Q))) H60 I) as R60.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  pose proof ST as (Lo0 & Hi64 & _).
  do 2 step. ifc false.
  do 3 step. ifc false.
  do 4 step.
  eapply evt_cut;
    [ eapply (ul_rd32 RD) with (Fc := Fc) (b := b) (swz := swz) (q := Q) (j := 12);
      first [ assumption | (apply ul_sx32_01; assumption) | reflexivity | (f_equal; lia) | lia ]
    | rd_post ].
  rewrite <- ESW. change (hw sw Fc Q 12) with (orig sw Fc Q).
  step. rewrite (ul_sx32_sw (orig sw Fc Q)) by lia. ifc false.
  do 3 step. rewrite ltu_swrap by lia.
  destruct (Z.ltb_spec (incl sw Fc Q) 18) as [T18|T18]; cbv iota.
  (* incl < 18: untagged *)
  { assert (TG : tagged sw Fc Q = false) by (unfold tagged, fb; bool_dec; reflexivity).
    rewrite TG in H64. cbv iota in H64.
    pose proof (ul_ro _ _ (C4 (Z_to_bv 64 0)) H64 I) as R64.
    do 3 step. ifc false. step. ifc true.
    eapply ul_L_unt; first [ eassumption | reflexivity | (f_equal; lia) | lia ]. }
  do 2 step. ifc false.
  pose proof (bytes_at_byte m b Fc (Q + 28) HB ltac:(lia)) as HR28.
  pose proof (byte_range (nth (Z.to_nat (Q + 28)) Fc (Z_to_bv 8 0))) as BR28.
  do 3 step.
  destruct (Z.eqb_spec (fb Fc (Q + 28)) 129) as [T28|T28]; unfold fb in T28.
  2: { (* the byte 12 of the frame is not 0x81: untagged *)
    ifc true.
    assert (TG : tagged sw Fc Q = false) by (unfold tagged, fb; bool_dec; reflexivity).
    rewrite TG in H64. cbv iota in H64.
    pose proof (ul_ro _ _ (C4 (Z_to_bv 64 0)) H64 I) as R64.
    do 3 step. ifc false. step. ifc true.
    eapply ul_L_unt; first [ eassumption | reflexivity | (f_equal; lia) | lia ]. }
  ifc false.
  do 2 step. ifc false.
  pose proof (bytes_at_byte m b Fc (Q + 29) HB ltac:(lia)) as HR29.
  pose proof (byte_range (nth (Z.to_nat (Q + 29)) Fc (Z_to_bv 8 0))) as BR29.
  do 2 step.
  destruct (Z.eqb_spec (fb Fc (Q + 29)) 0) as [T29|T29]; unfold fb in T29.
  2: { (* the byte 13 of the frame is not 0: untagged *)
    rep_reg 10 (Z_to_bv 64 0)
      ltac:(rewrite v_sltiu_b2z, zxb_val; change (bv_wrap 64 1) with 1; rewrite (proj2 (Z.ltb_ge _ _)) by lia;
            reflexivity).
    assert (TG : tagged sw Fc Q = false) by (unfold tagged, fb; bool_dec; reflexivity).
    rewrite TG in H64. cbv iota in H64.
    pose proof (ul_ro _ _ (C4 (Z_to_bv 64 0)) H64 I) as R64.
    do 3 step. ifc false. step. ifc true.
    eapply ul_L_unt; first [ eassumption | reflexivity | (f_equal; lia) | lia ]. }
  (* tagged: 0x81 0x00 after the MAC addresses *)
  rep_reg 10 (Z_to_bv 64 1)
    ltac:(rewrite v_sltiu_b2z, zxb_val; change (bv_wrap 64 1) with 1; rewrite (proj2 (Z.ltb_lt _ _)) by lia;
          reflexivity).
  assert (TG : tagged sw Fc Q = true) by (unfold tagged, fb; bool_dec; reflexivity).
  rewrite TG in H64, H68. cbv iota in H64, H68.
  pose proof (ul_ro _ _ (C4 (Z_to_bv 64 1)) H64 I) as R64.
  pose proof (ul_ro _ _ (C2 (Z_to_bv 64 (rec_vid Fc Q))) H68 I) as R68.
  assert (RLT : rec_len sw Fc Q = incl sw Fc Q - 4) by (unfold rec_len; rewrite TG; reflexivity).
  rewrite RLT.
  pose proof (ul_rec_raw_len sw Fc Q HQ KQ1) as LRAW.
  rewrite (ul_rb_tag sw Fc Q TG) in HBUF.
  pose proof (ul_bytes_sub m b Fc (Z.to_nat (Q + 16)) (Z.to_nat (incl sw Fc Q)) (b + Q + 16) HB ltac:(lia) ltac:(lia))
    as HRAW.
  change (firstn (Z.to_nat (incl sw Fc Q)) (skipn (Z.to_nat (Q + 16)) Fc)) with (rec_raw sw Fc Q) in HRAW.
  pose proof (ul_bytes_sub m (b + Q + 16) (rec_raw sw Fc Q) 0 12 (b + Q + 16) HRAW ltac:(lia) ltac:(lia)) as HR12.
  change (skipn 0 (rec_raw sw Fc Q)) with (rec_raw sw Fc Q) in HR12.
  pose proof (ul_bytes_sub m (b + Q + 16) (rec_raw sw Fc Q) 16 (Z.to_nat (incl sw Fc Q - 16)) (b + Q + 32) HRAW
                ltac:(lia) ltac:(lia)) as HR16.
  pose proof HBUF as HB2. apply bytes_at_app in HB2. destruct HB2 as [_ HB2].
  rewrite length_firstn, LRAW in HB2.
  replace (buf + Z.of_nat (Nat.min 12 (Z.to_nat (incl sw Fc Q)))) with (buf + 12) in HB2 by lia.
  assert (RV : 0 <= rec_vid Fc Q < 4096) by (unfold rec_vid; apply Z.mod_pos_bound; lia).
  do 3 step. ifc false. step. ifc false.
  do 3 step.
  rep_reg 10 (Z_to_bv 64 (incl sw Fc Q - 4)) ltac:(zx_eq).
  step. ifc false.
  do 4 step.
  eapply evt_cut; [eapply BC | ].
  { unwrap. exact HBUF. }
  { unwrap. exact HR12. }
  { change (Z.to_nat (bv_unsigned (Z_to_bv 64 12))) with 12%nat. apply ul_mcm_pre. rewrite length_firstn. lia. }
  { exact MI. }
  post_call rsegs m.
  step. ifc false.
  do 3 step. ifc false.
  do 2 step. ifc false.
  do 4 step.
  rep_reg 12 (Z_to_bv 64 (incl sw Fc Q - 16)) ltac:(zx_eq).
  do 2 step.
  let mm := cur_mem in
  eapply evt_cut;
    [ eapply BC;
      [ unwrap; exact HB2
      | unwrap; exact HR16
      | unwrap; apply ul_mcm_pre; rewrite length_firstn, length_skipn, LRAW; lia
      | assumption ]
    | post_call rsegs mm ].
  step. ifc false.
  do 2 step. ifc false.
  do 2 step. ifc false.
  let mm := cur_mem in
  pose proof (bytes_at_byte mm b Fc (Q + 30) HB ltac:(lia)) as HR30;
  pose proof (bytes_at_byte mm b Fc (Q + 31) HB ltac:(lia)) as HR31.
  do 3 step.
  rep_reg 12 (Z_to_bv 64 (rec_vid Fc Q))
    ltac:(unfold zx16; f_equal; rewrite unsigned_lit by lia; symmetry; apply Z.mod_small; lia).
  do 3 step.
  rep_reg 10 (Z_to_bv 64 (rec_vid Fc Q)) ltac:(unfold rec_vid, fb; rewrite vid_lor by apply byte_range; bits_eq).
  step. ifc false.
  step.
  eapply ul_L_ts; first [ eassumption | reflexivity | (f_equal; lia) | lia ].
Qed.

(* L: K4 0x12e38 (loop index i, file position q, record Q) to the pcap_source_next call at 0x13030
   (fuzz/fuzz_pcap.c:137-216): the count check, the skip loop, the record checks, calls = i + 1, ts = -1 and the
   next position Q + 16 + incl. *)
Lemma ubs_L_x : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                         t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
                         (Fc : list byte) (sw : bool) (lo sp_h b buf cap swz i q Q first : Z),
  rd32f_contract -> bcmp_contract ->
  bv_unsigned sp = sp_h -> s9 = wz q -> s0 = wz b -> s1 = wz cap -> s2 = wz (-8) -> s4 = bv_not (wz b) ->
  s5 = wz (rec_len sw Fc Q) -> s10 = wz (symaddr Symbols.Ubsan.s_g_file_len) -> s11 = wz first ->
  ((i = 0 /\ first = rec_len sw Fc Q) \/ (0 < i /\ a3 = wz first)) -> 0 <= i -> 24 + 17 * i <= q ->
  skips sw Fc cap q Q -> kind sw Fc cap Q = KFit ->
  Z.of_nat (length Fc) < 2 ^ 26 -> b <> 0 -> b + Z.of_nat (length Fc) < 2 ^ 63 ->
  bytes_at rsegs m (symaddr Symbols.Ubsan.s_g_file_len) (le8 (wz (Z.of_nat (length Fc)))) -> bytes_at rsegs m b Fc -> 0 <= cap <= 2040 ->
  bytes_at rsegs m (sp_h + 8) (le8 (wz (buf + 12))) -> bytes_at rsegs m (sp_h + 16) (le8 (wz (1000000 * 2 ^ 32))) ->
  bytes_at rsegs m (sp_h + 24) (le8 (wz buf)) ->
  rw_cells rsegs m (sp_h + 32) [C8 (wz i)] -> rw_cells rsegs m (sp_h + 40) [C8 (wz (rec_ts sw Fc Q))] ->
  bytes_at rsegs m (sp_h + 56) (le4 (wz swz)) -> (swz = 0 \/ swz = 1) -> sw = (swz =? 1) ->
  bytes_at rsegs m (sp_h + 60) (le4 (wz (orig sw Fc Q))) ->
  bytes_at rsegs m (sp_h + 64) (le4 (wz (if tagged sw Fc Q then 1 else 0))) ->
  bytes_at rsegs m (sp_h + 68) (le2 (wz (if tagged sw Fc Q then rec_vid Fc Q else 0))) ->
  bytes_at rsegs m buf (rec_bytes sw Fc Q) -> 4096 <= buf -> buf + 2040 < 2 ^ 63 ->
  (b + Z.of_nat (length Fc) <= sp_h \/ sp_h + 176 <= b) -> (buf + 2040 <= sp_h \/ sp_h + 176 <= buf) ->
  (symaddr Symbols.Ubsan.s_g_file) <= sp_h ->
  mem_inv rsegs m -> stk rsegs m lo (sp_h + 176) ->
  evt rsegs (QL sp gp tp s0 s1 s2 s4 s10 s11 F fc m lo sp_h buf cap (Q + 16 + incl sw Fc Q) (wz (i + 1)))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0x1ec)%Z)) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m Fc sw lo sp_h b buf cap swz i q Q first RD BC HSP E9 E0 E1 E2 E4 E5 E10 E11 HI Hi Hq SK KQ HN Hb HBN
    HBL HB HC H8 H16 H24 H32 H40 H56 HSW ESW H60 H64 H68 HBUF Hbuf Hbuf2 DB DBUF DG MI ST.
  subst sp_h s9 s0 s1 s2 s4 s5 s10 s11. unfold wz in *.
  pose proof (bytes_at_bound rsegs _ _ _ HB) as BB.
  pose proof (kind_fit _ _ _ _ KQ) as (_ & KR & _ & KQ1 & KQ2). unfold flen in KQ1.
  pose proof (skips_le _ _ _ _ _ SK) as LQ.
  pose proof (ul_rec_bytes_len sw Fc Q ltac:(lia) KQ1) as LRB.
  assert (KD : i + 1 <= (Z.of_nat (length Fc) - 24) / 16) by (apply Z.div_le_lower_bound; lia).
  assert (KD2 : (Z.of_nat (length Fc) - 24) / 16 <= Z.of_nat (length Fc) - 24)
    by (apply Z.div_le_upper_bound; lia).
  pose proof (ul_ro _ _ (C8 (Z_to_bv 64 (Z.of_nat (length Fc)))) HBL I) as RL.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  pose proof ST as (Lo0 & Hi64 & _).
  pose proof (munch_refl [(bv_unsigned sp + 32, bv_unsigned sp + 48)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  do 3 step.
  rep_reg 12 (Z_to_bv 64 ((Z.of_nat (length Fc) - 24) / 16))
    ltac:(f_equal; unwrap; rewrite Z.shiftr_div_pow2 by lia; change (2 ^ 4) with 16; f_equal; lia).
  do 2 step. ifc false.
  do 3 step.
  destruct HI as [(Hi0 & Ef) | (Hi0 & E3)];
    [ ifc true; rep_reg 27 (Z_to_bv 64 first) ltac:(f_equal; lia) | subst a3; ifc false; step ].
  all: step; ifc false; step; step; ifc false; step; ifc false; do 3 step;
      (eapply evt_cut; [ eapply (ubs_L_skip sw Fc cap q Q RD SK); first [ eassumption | reflexivity | lia ] | ]);
      let ms' := fresh "ms'" in intros ms' (? & ? & ? & ? & ? & ? & ? & ->);
      eapply ul_L_rec; first [ eassumption | reflexivity | (f_equal; lia) | lia ].
Qed.
