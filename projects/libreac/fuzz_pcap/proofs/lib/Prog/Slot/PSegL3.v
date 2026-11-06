From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import SymAddr.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Lib Require Import PropExec MState Mem Cells Exec Frame Step Tac Bytes ZBridge Arr.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog Require Import StdioModel bcmp_c
  pcap_source_struct pcap_source_struct_next pcap_source_next_lib.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog.Slot Require Import PWalkDef PSegL PSegL2.
Import ListNotations.
Open Scope Z_scope.

Lemma sx32_small : forall z, 0 <= z < 2 ^ 31 -> sx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof. intros z Hz. unfold sx32. rewrite unsigned_lit by lia. f_equal. rewrite swrap32_eq. rewrite Z.mod_small by lia. lia. Qed.

Lemma sx32_lit : forall z, 0 <= z < 2 ^ 64 -> sx32 (Z_to_bv 64 z) = Z_to_bv 64 (bv_swrap 32 z).
Proof. intros z Hz. unfold sx32. rewrite unsigned_lit by lia. reflexivity. Qed.

Lemma zx16_small : forall z, 0 <= z < 2 ^ 16 -> zx16 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof. intros z Hz. unfold zx16. rewrite unsigned_lit by lia. rewrite Z.mod_small by lia. reflexivity. Qed.

Lemma bytes_drop : forall m A l k, bytes_at rsegs m A l -> 0 <= k <= Z.of_nat (length l) ->
  bytes_at rsegs m (A + k) (skipn (Z.to_nat k) l).
Proof.
  intros m A l k H Hk. rewrite <- (firstn_skipn (Z.to_nat k) l) in H. apply bytes_at_app in H.
  destruct H as [_ H]. rewrite length_firstn in H.
  replace (A + Z.of_nat (Nat.min (Z.to_nat k) (length l))) with (A + k) in H by lia. exact H.
Qed.

Lemma mcm_zero : forall n l r, (n <= length l)%nat -> (n <= length r)%nat -> firstn n l = firstn n r ->
  memcmp_model l r n = Some 0.
Proof.
  induction n as [|n IH]; intros [|x l] [|y r] Hl Hr E; cbn in *; try lia; try reflexivity.
  injection E as Exy E. subst y. rewrite Z.eqb_refl. apply IH; [lia | lia | exact E].
Qed.

Lemma rec_raw_len : forall sw Fc Q, 0 <= Q -> Q + 16 + incl sw Fc Q <= Z.of_nat (length Fc) ->
  length (rec_raw sw Fc Q) = Z.to_nat (incl sw Fc Q).
Proof.
  intros sw Fc Q H0 H1. unfold rec_raw. rewrite length_firstn, length_skipn.
  pose proof (hw_range sw Fc Q 8). unfold incl in *. lia.
Qed.

Lemma rec_raw_pre : forall sw Fc Q n, (n <= Z.to_nat (incl sw Fc Q))%nat ->
  firstn n (rec_raw sw Fc Q) = firstn n (skipn (Z.to_nat (Q + 16)) Fc).
Proof. intros sw Fc Q n H. unfold rec_raw. rewrite firstn_firstn. f_equal. lia. Qed.

Lemma tagged_18 : forall sw Fc Q, tagged sw Fc Q = true -> 18 <= incl sw Fc Q.
Proof.
  intros sw Fc Q TG. unfold tagged in TG. apply andb_true_iff in TG as [TG _].
  apply andb_true_iff in TG as [TG _]. apply Z.leb_le in TG. exact TG.
Qed.

Lemma rec_bytes_len : forall sw Fc Q, 0 <= Q -> Q + 16 + incl sw Fc Q <= Z.of_nat (length Fc) ->
  length (rec_bytes sw Fc Q) = Z.to_nat (incl sw Fc Q).
Proof.
  intros sw Fc Q H0 H1. pose proof (rec_raw_len sw Fc Q H0 H1) as L. unfold rec_bytes.
  destruct (tagged sw Fc Q) eqn:TG; cbv beta iota zeta; [|exact L].
  pose proof (tagged_18 sw Fc Q TG) as T.
  rewrite !length_app, !length_firstn, !length_skipn, L. lia.
Qed.

Lemma rec_untag : forall sw Fc Q, tagged sw Fc Q = false -> rec_bytes sw Fc Q = rec_raw sw Fc Q.
Proof. intros sw Fc Q TG. unfold rec_bytes. rewrite TG. reflexivity. Qed.

Lemma rec_tag1 : forall sw Fc Q, tagged sw Fc Q = true -> 0 <= Q -> Q + 16 + incl sw Fc Q <= Z.of_nat (length Fc) ->
  firstn 12 (rec_bytes sw Fc Q) = firstn 12 (skipn (Z.to_nat (Q + 16)) Fc).
Proof.
  intros sw Fc Q TG H0 H1. pose proof (rec_raw_len sw Fc Q H0 H1) as L. pose proof (tagged_18 sw Fc Q TG) as T.
  unfold rec_bytes. rewrite TG. cbv beta iota zeta.
  rewrite firstn_app, length_firstn, L. replace (12 - Nat.min 12 (Z.to_nat (incl sw Fc Q)))%nat with 0%nat by lia.
  rewrite firstn_O, app_nil_r, firstn_firstn, Nat.min_id. apply rec_raw_pre. lia.
Qed.

Lemma rec_tag2 : forall sw Fc Q, tagged sw Fc Q = true -> 0 <= Q -> Q + 16 + incl sw Fc Q <= Z.of_nat (length Fc) ->
  firstn (Z.to_nat (incl sw Fc Q - 16)) (skipn 12 (rec_bytes sw Fc Q)) =
  firstn (Z.to_nat (incl sw Fc Q - 16)) (skipn (Z.to_nat (Q + 32)) Fc).
Proof.
  intros sw Fc Q TG H0 H1. pose proof (rec_raw_len sw Fc Q H0 H1) as L. pose proof (tagged_18 sw Fc Q TG) as T.
  unfold rec_bytes. rewrite TG. cbv beta iota zeta.
  rewrite skipn_app, length_firstn, L. replace (12 - Nat.min 12 (Z.to_nat (incl sw Fc Q)))%nat with 0%nat by lia.
  rewrite skipn_O, (skipn_all2 (firstn 12 (rec_raw sw Fc Q))) by (rewrite length_firstn; lia). cbn [app].
  rewrite firstn_app, length_firstn, length_skipn, L.
  replace (Z.to_nat (incl sw Fc Q - 16) - Nat.min (Z.to_nat (incl sw Fc Q - 16)) (Z.to_nat (incl sw Fc Q) - 16))%nat
    with 0%nat by lia.
  rewrite firstn_O, app_nil_r, firstn_firstn, Nat.min_id.
  unfold rec_raw. rewrite skipn_firstn_comm, firstn_firstn, skipn_skipn.
  replace (Nat.min (Z.to_nat (incl sw Fc Q - 16)) (Z.to_nat (incl sw Fc Q) - 16)) with (Z.to_nat (incl sw Fc Q - 16)) by lia.
  f_equal. f_equal. lia.
Qed.

Lemma zx_swrap_add : forall I d, 0 <= I < 2 ^ 31 -> 0 <= I + d < 2 ^ 32 ->
  Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 (bv_swrap 32 I + d))) 32))) 32) =
  Z_to_bv 64 (I + d).
Proof.
  intros I d HI Hd. f_equal.
  assert (E : bv_swrap 32 I = I) by (rewrite swrap32_eq; rewrite Z.mod_small by lia; lia).
  rewrite E, (unsigned_lit (I + d)) by lia. rewrite Z.shiftl_mul_pow2 by lia.
  rewrite (unsigned_lit ((I + d) * 2 ^ 32)) by lia. rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_mul by lia.
  reflexivity.
Qed.

Lemma rec_vid_range : forall Fc Q, 0 <= rec_vid Fc Q < 2 ^ 16.
Proof. intros Fc Q. unfold rec_vid. pose proof (Z.mod_pos_bound (256 * fb Fc (Q + 30) + fb Fc (Q + 31)) 4096). lia. Qed.

(* A call of bcmp on the byte lists ls and rs: t1, t2, t3 prove the two byte ranges and the memcmp_model answer 0. *)
Ltac bcmp_call B L R t1 t2 t3 :=
  lazymatch goal with
  | |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
      eapply evt_cut; [ eapply B with (ls := L) (rs := R) (v := 0); [ t1 | t2 | t3 | assumption ] | post_call segs mm ]
  end.

(* 0x12ef8-0x12f6c for a record with a VLAN tag: two bcmp calls (12 bytes, then the rest after the tag) and the
   vid check; then the tail. *)
Lemma pcap_L_tagd : bcmp_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m0 m : word -> option byte) (sw : bool) (Fc pad : list byte)
         (lo sp_h cap buf b first Q i swz h : Z),
  bv_unsigned sp = sp_h -> s0 = wz (b + Q) -> s1 = wz cap -> s2 = wz buf -> s3 = wz first -> s4 = wz b ->
  s5 = wz 0xff00 -> s6 = wz (symaddr Symbols.Plain.s_g_file_len) -> s7 = wz (bv_swrap 32 (incl sw Fc Q)) -> s8 = wz Q -> s9 = wz (i + 1) ->
  s10 = wz swz -> s11 = wz (1000000 * 2 ^ 32) -> sw = (swz =? 1) -> (swz = 0 \/ swz = 1) ->
  a0 = wz 1 -> a2 = wz (rec_len sw Fc Q) -> tagged sw Fc Q = true ->
  0 <= Q -> Q + 16 + incl sw Fc Q <= Z.of_nat (length Fc) -> incl sw Fc Q <= 2040 ->
  Z.of_nat (length Fc) < 2 ^ 26 -> bytes_at rsegs m b Fc -> bytes_at rsegs m buf (rec_bytes sw Fc Q) ->
  rw_cells rsegs m (sp_h + 32) [C8 (wz h); C4 (wz swz); C4 (wz (orig sw Fc Q)); C4 (wz 1); C2 (wz (rec_vid Fc Q)); CB 2 pad] ->
  rw_cells rsegs m (sp_h + 16) [C8 (wz (buf + 12))] -> rw_cells rsegs m (sp_h + 24) [C8 (wz (rec_ts sw Fc Q))] ->
  munch [(sp_h + 24, sp_h + 32)] m0 m -> wmono rsegs m0 m -> mem_inv rsegs m -> stk rsegs m lo (sp_h + 160) ->
  evt rsegs (QL sp gp tp F fc m0 lo sp_h cap buf b first (Q + 16 + incl sw Fc Q) i)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 (symaddr (Symbols.Plain.s_LLVMFuzzerTestOneInput + 0x2f4)%Z)) fc None m (seg_rom rsegs)).
Proof.
  intros BCMPc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m0 m sw Fc pad lo sp_h cap buf b first Q i swz h HSP E0 E1 E2 E3 E4 E5 E6 E7 E8 E9 E10 E11 ESW HSW
    EA0 EA2 TG HQ HQL HI HN HB HBUF HPS H16 HTS MU WM MI ST.
  subst sp_h s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 a2. unfold wz in *.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  pose proof (bytes_at_bound rsegs _ _ _ HB) as BB.
  pose proof (bytes_at_bound rsegs _ _ _ HBUF) as BBUF. rewrite (rec_bytes_len sw Fc Q HQ HQL) in BBUF.
  pose proof (rec_bytes_len sw Fc Q HQ HQL) as LRB.
  pose proof (tagged_18 _ _ _ TG) as T18.
  assert (RLT : rec_len sw Fc Q = incl sw Fc Q - 4) by (unfold rec_len; rewrite TG; reflexivity).
  assert (ER : bv_unsigned (Z_to_bv 64 (rec_len sw Fc Q)) = rec_len sw Fc Q) by (apply unsigned_lit; lia).
  assert (E4 : bv_unsigned (Z_to_bv 64 (incl sw Fc Q + -4)) = incl sw Fc Q + -4) by (apply unsigned_lit; lia).
  pose proof (rec_vid_range Fc Q) as RV.
  step. step. if_false. do 3 step.
  rewrite (zx_swrap_add (incl sw Fc Q) (-4)) by lia.
  step. if_false.
  do 3 step.
  bcmp_call BCMPc (rec_bytes sw Fc Q) (skipn (Z.to_nat (Q + 16)) Fc)
    ltac:(rewrite unsigned_lit by lia; exact HBUF)
    ltac:(rewrite unsigned_lit by lia; replace (b + Q + 16) with (b + (Q + 16)) by lia; apply bytes_drop; [exact HB | lia])
    ltac:(change (bv_unsigned (Z_to_bv 64 12)) with 12; change (Z.to_nat 12) with 12%nat;
          apply mcm_zero; [rewrite LRB; lia | rewrite length_skipn; lia | apply rec_tag1; [exact TG | lia | lia]]).
  step. if_false.
  step. do 3 step.
  rewrite (zx_swrap_add (incl sw Fc Q) (-16)) by lia.
  step. step.
  bcmp_call BCMPc (skipn (Z.to_nat 12) (rec_bytes sw Fc Q)) (skipn (Z.to_nat (Q + 32)) Fc)
    ltac:(rewrite unsigned_lit by lia; apply (bytes_drop _ _ _ 12); [exact HBUF | lia])
    ltac:(rewrite unsigned_lit by lia; replace (b + Q + 32) with (b + (Q + 32)) by lia; apply bytes_drop; [exact HB | lia])
    ltac:(rewrite unsigned_lit by lia; replace (incl sw Fc Q + -16) with (incl sw Fc Q - 16) by lia;
          change (Z.to_nat 12) with 12%nat;
          apply mcm_zero; [rewrite length_skipn, LRB; lia | rewrite length_skipn; lia | apply rec_tag2; [exact TG | lia | lia]]).
  step. if_false.
  pose proof (bytes_at_byte _ b Fc (Q + 30) HB ltac:(lia)) as HB30.
  pose proof (bytes_at_byte _ b Fc (Q + 31) HB ltac:(lia)) as HB31.
  do 3 step. rewrite zx16_small by lia.
  do 3 step.
  rep_reg 10 (Z_to_bv 64 (rec_vid Fc Q)) ltac:(unfold rec_vid, fb; rewrite vid_lor by apply byte_range; bits_eq).
  step. if_false. step.
  eapply pcap_L_tail; first [ reflexivity | exact ESW | exact HSW | eassumption | lia ].
Qed.

(* 0x12ef8-0x12f6c for a record without a VLAN tag: one bcmp call over incl bytes; then the tail. *)
Lemma pcap_L_untag : bcmp_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m0 m : word -> option byte) (sw : bool) (Fc : list byte)
         (lo sp_h cap buf b first Q i swz : Z),
  bv_unsigned sp = sp_h -> s0 = wz (b + Q) -> s1 = wz cap -> s2 = wz buf -> s3 = wz first -> s4 = wz b ->
  s5 = wz 0xff00 -> s6 = wz (symaddr Symbols.Plain.s_g_file_len) -> s7 = wz (bv_swrap 32 (incl sw Fc Q)) -> s8 = wz Q -> s9 = wz (i + 1) ->
  s10 = wz swz -> s11 = wz (1000000 * 2 ^ 32) -> sw = (swz =? 1) -> (swz = 0 \/ swz = 1) ->
  a0 = wz 0 -> a2 = wz (rec_len sw Fc Q) -> a3 = wz (incl sw Fc Q) -> tagged sw Fc Q = false ->
  0 <= Q -> Q + 16 + incl sw Fc Q <= Z.of_nat (length Fc) -> 1 <= incl sw Fc Q <= 2040 ->
  Z.of_nat (length Fc) < 2 ^ 26 -> bytes_at rsegs m b Fc -> bytes_at rsegs m buf (rec_bytes sw Fc Q) ->
  rw_cells rsegs m (sp_h + 24) [C8 (wz (rec_ts sw Fc Q))] ->
  munch [(sp_h + 24, sp_h + 32)] m0 m -> wmono rsegs m0 m -> mem_inv rsegs m -> stk rsegs m lo (sp_h + 160) ->
  evt rsegs (QL sp gp tp F fc m0 lo sp_h cap buf b first (Q + 16 + incl sw Fc Q) i)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 (symaddr (Symbols.Plain.s_LLVMFuzzerTestOneInput + 0x2f4)%Z)) fc None m (seg_rom rsegs)).
Proof.
  intros BCMPc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m0 m sw Fc lo sp_h cap buf b first Q i swz HSP E0 E1 E2 E3 E4 E5 E6 E7 E8 E9 E10 E11 ESW HSW
    EA0 EA2 EA3 TG HQ HQL HI HN HB HBUF HTS MU WM MI ST.
  subst sp_h s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 a2 a3. unfold wz in *.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  pose proof (bytes_at_bound rsegs _ _ _ HB) as BB.
  pose proof (bytes_at_bound rsegs _ _ _ HBUF) as BBUF. rewrite (rec_bytes_len sw Fc Q HQ HQL) in BBUF.
  pose proof (rec_bytes_len sw Fc Q HQ HQL) as LRB.
  assert (RLU : rec_len sw Fc Q = incl sw Fc Q) by (unfold rec_len; rewrite TG; reflexivity).
  assert (ER : bv_unsigned (Z_to_bv 64 (rec_len sw Fc Q)) = rec_len sw Fc Q) by (apply unsigned_lit; lia).
  assert (EI : bv_unsigned (Z_to_bv 64 (incl sw Fc Q)) = incl sw Fc Q) by (apply unsigned_lit; lia).
  step. step. if_true.
  step. if_false.
  do 2 step.
  bcmp_call BCMPc (rec_bytes sw Fc Q) (skipn (Z.to_nat (Q + 16)) Fc)
    ltac:(rewrite unsigned_lit by lia; exact HBUF)
    ltac:(rewrite unsigned_lit by lia; replace (b + Q + 16) with (b + (Q + 16)) by lia; apply bytes_drop; [exact HB | lia])
    ltac:(rewrite ER, RLU;
          apply mcm_zero; [rewrite LRB; lia | rewrite length_skipn; lia |
                           rewrite (rec_untag _ _ _ TG); apply rec_raw_pre; lia]).
  step. if_false.
  eapply pcap_L_tail; first [ reflexivity | exact ESW | exact HSW | eassumption | lia ].
Qed.

(* Segment L: from the loop head K4 (0x12dcc, record i at file position p) to the next call of
   pcap_source_next (0x132a0, return address 0x13044). No check branches to the stop call 0x131c4. *)
Lemma pcap_L_x : bcmp_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (sw : bool) (Fc pad : list byte)
         (lo sp_h cap buf b p i Q first swz h : Z),
  bv_unsigned sp = sp_h -> s1 = wz cap -> 0 <= cap <= 2040 -> s2 = wz buf -> s4 = wz b ->
  s6 = wz (symaddr Symbols.Plain.s_g_file_len) -> bytes_at rsegs m (symaddr Symbols.Plain.s_g_file_len) (le8 (wz (Z.of_nat (length Fc)))) ->
  s5 = wz 0xff00 -> s11 = wz (1000000 * 2 ^ 32) -> s8 = wz p -> s9 = wz i -> 0 <= i -> 24 + 17 * i <= p ->
  skips sw Fc cap p Q -> kind sw Fc cap Q = KFit -> a2 = wz (rec_len sw Fc Q) ->
  (i = 0 /\ rec_len sw Fc Q = first \/ 0 < i /\ a1 = wz first) ->
  sw = (swz =? 1) -> (swz = 0 \/ swz = 1) -> Z.of_nat (length Fc) < 2 ^ 26 -> bytes_at rsegs m b Fc ->
  rw_cells rsegs m (sp_h + 32)
    (ps_cells (wz h) (wz swz) (wz (orig sw Fc Q)) (if tagged sw Fc Q then wz 1 else wz 0)
              (if tagged sw Fc Q then wz (rec_vid Fc Q) else wz 0) pad) ->
  rw_cells rsegs m (sp_h + 16) [C8 (wz (buf + 12))] ->
  rw_cells rsegs m (sp_h + 24) [C8 (wz (rec_ts sw Fc Q))] ->
  bytes_at rsegs m buf (rec_bytes sw Fc Q) ->
  mem_inv rsegs m -> stk rsegs m lo (sp_h + 160) ->
  evt rsegs (QL sp gp tp F fc m lo sp_h cap buf b first (Q + 16 + incl sw Fc Q) i)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 (symaddr (Symbols.Plain.s_LLVMFuzzerTestOneInput + 0x1c8)%Z)) fc None m (seg_rom rsegs)).
Proof.
  intros BCMPc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m sw Fc pad lo sp_h cap buf b p i Q first swz h
    HSP E1 HC E2 E4 E6 HFLB E5 E11 E8 E9 Hi0 Hip SK KQ EA2 HFST ESW HSW HN HB HPS H16 HTS HBUF MI ST.
  subst sp_h s1 s2 s4 s6 s5 s11 s8 s9 a2. unfold wz in *.
  pose proof (kind_fit_facts _ _ _ _ KQ) as (KF1 & KF2 & KF3).
  pose proof (skips_le _ _ _ _ _ SK) as LQ.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  pose proof (bytes_at_bound rsegs _ _ _ HB) as BB.
  assert (RL : 0 <= rec_len sw Fc Q <= incl sw Fc Q).
  { unfold rec_len. destruct (tagged sw Fc Q) eqn:TG; [|lia]. unfold tagged in TG.
    apply andb_true_iff in TG as [TG _]. apply andb_true_iff in TG as [TG _]. apply Z.leb_le in TG. lia. }
  pose proof (bytes_at_ov_read rsegs m (symaddr Symbols.Plain.s_g_file_len) (le8 (Z_to_bv 64 (Z.of_nat (length Fc)))) 0 8 HFLB
                ltac:(rewrite length_le8; lia)) as HFL.
  change (skipn 0 (le8 (Z_to_bv 64 (Z.of_nat (length Fc))))) with (le8 (Z_to_bv 64 (Z.of_nat (length Fc)))) in HFL.
  rewrite firstn_all2 in HFL by (rewrite length_le8; lia).
  replace ((symaddr Symbols.Plain.s_g_file_len) + Z.of_nat 0) with (symaddr Symbols.Plain.s_g_file_len) in HFL by reflexivity.
  pose proof (munch_refl [(bv_unsigned sp + 24, bv_unsigned sp + 32)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  unfold ps_cells in HPS.
  set (flen := Z.of_nat (length Fc)) in *.
  assert (EIi : bv_unsigned (Z_to_bv 64 i) = i) by (apply unsigned_lit; lia).
  assert (IQ : i < (flen - 24) / 16).
  { assert (i + 1 <= (flen - 24) / 16) by (apply Z.div_le_lower_bound; lia). lia. }
  assert (EQ16 : bv_unsigned (Z_to_bv 64 ((flen - 24) / 16)) = (flen - 24) / 16).
  { apply unsigned_lit. split; [apply Z.div_pos; lia | apply (Z.le_lt_trans _ flen); [apply Z.div_le_upper_bound; lia | lia]]. }
  assert (EC : bv_unsigned (Z_to_bv 64 cap) = cap) by (apply unsigned_lit; lia).
  assert (ER : bv_unsigned (Z_to_bv 64 (rec_len sw Fc Q)) = rec_len sw Fc Q) by (apply unsigned_lit; lia).
  assert (EF : bv_unsigned (Z_to_bv 64 flen) = flen) by (apply unsigned_lit; lia).
  assert (EP16 : bv_unsigned (Z_to_bv 64 (p + 16)) = p + 16) by (apply unsigned_lit; lia).
  do 3 step.
  rep_reg 13 (Z_to_bv 64 ((flen - 24) / 16))
    ltac:(f_equal; rewrite unsigned_lit by lia; rewrite Z.shiftr_div_pow2 by lia;
          replace (2 ^ 4) with 16 by reflexivity; f_equal; lia).
  step. if_false.
  step. step.
  eapply evt_cut with (P := fun ms => exists a1' : word,
    ms = MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 cap) (Z_to_bv 64 flen) a1' (Z_to_bv 64 (rec_len sw Fc Q))
                 (Z_to_bv 64 ((flen - 24) / 16)) a4 a5 a6 a7 (Z_to_bv 64 buf) (Z_to_bv 64 first) (Z_to_bv 64 b)
                 (Z_to_bv 64 0xff00) (Z_to_bv 64 (symaddr Symbols.Plain.s_g_file_len)) s7 (Z_to_bv 64 p) (Z_to_bv 64 i) s10
                 (Z_to_bv 64 (1000000 * 2 ^ 32)) t3 t4 t5 t6) F (Z_to_bv 64 (symaddr (Symbols.Plain.s_LLVMFuzzerTestOneInput + 0x1e4)%Z)) fc None m (seg_rom rsegs)).
  { destruct HFST as [[I0 RF]|[IP EA1]].
    - subst i. if_true. apply evt_done. eexists. rewrite <- RF. reflexivity.
    - subst a1. if_false. step. apply evt_done. eexists. reflexivity. }
  intros ms (a1' & ->). clear HFST.
  step. if_false.
  step. step. if_false.
  step. rewrite (sx32_small swz) by (destruct HSW; lia).
  step.
  subst flen.
  eapply evt_cut.
  { eapply (pcap_L_skip sw Fc cap p Q SK);
      first [ reflexivity | exact ESW | exact HSW | exact KQ | exact HN | exact HB | lia ]. }
  intros ms (s0' & a1'' & a3' & a4' & a5' & a6' & a7' & s7' & -> & -> & -> & -> & ->).
  clear SK. unfold wz.
  assert (EQI : bv_unsigned (Z_to_bv 64 (Q + 16 + incl sw Fc Q)) = Q + 16 + incl sw Fc Q) by (apply unsigned_lit; lia).
  step.
  step. if_false.
  pose proof (bytes_at_byte m b Fc (Q + 12) HB ltac:(lia)) as HB12.
  pose proof (bytes_at_byte m b Fc (Q + 13) HB ltac:(lia)) as HB13.
  pose proof (bytes_at_byte m b Fc (Q + 14) HB ltac:(lia)) as HB14.
  pose proof (bytes_at_byte m b Fc (Q + 15) HB ltac:(lia)) as HB15.
  pose proof (hw_range sw Fc Q 12) as RO. change (hw sw Fc Q 12) with (orig sw Fc Q) in RO.
  destruct HSW as [SW|SW]; subst swz;
   [do 11 step; if_true | do 11 step; if_false; do 8 step];
  rep_reg 11 (Z_to_bv 64 (bv_swrap 32 (orig sw Fc Q))) ltac:(rewrite ESW; hw_eq);
  step; rewrite (sx32_lit (orig sw Fc Q)) by lia;
  step; if_false.
  all: eapply evt_cut;
       [ eapply pcap_L_tag with (sw := sw) (Fc := Fc) (Q := Q) (b := b); first [ reflexivity | exact HB | lia ] | ];
       intros ms (a1t & ->).
  all: destruct (tagged sw Fc Q) eqn:TG; cbv beta iota in HPS;
       step; rewrite sx32_small by lia; step; if_false.
  1,3: eapply pcap_L_tagd;
       first [ exact BCMPc | reflexivity | exact ESW | exact TG | (left; reflexivity) | (right; reflexivity)
             | eassumption | lia ].
  all: eapply pcap_L_untag;
       first [ exact BCMPc | reflexivity | exact ESW | exact TG | (left; reflexivity) | (right; reflexivity)
             | eassumption | lia ].
Qed.
