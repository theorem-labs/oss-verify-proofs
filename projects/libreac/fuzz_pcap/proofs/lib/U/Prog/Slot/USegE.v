From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import SymAddr.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Lib Require Import PropExec MState Mem Cells Exec Frame Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Prog Require Import StdioModel memcpy_c rd_u32_c rd32f_c.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog Require Import pcap_source_struct.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Prog.Slot Require Import USegR7.
Import ListNotations.
Open Scope Z_scope.

(* Segments E0, E, A, B and C of the fuzz_pcap ubsan slot: entry_fn (LLVMFuzzerTestOneInput, 0x12c4c) from its
   entry to the return (payload of 2^26 bytes or more) or to the malloc of the file copy, then to the calls of
   pcap_source_open, malloc of the record buffer (or free of the refused file copy) and the first
   pcap_source_next. S = sp_h + 176 is the sp at entry; the prologue saves ra, s0-s11 at sp_h + 72 (ubs_saved). *)

Lemma shr26_ne0 : forall u, 67108864 <= u < 18446744073709551616 ->
  negb (bv_eqb (Z_to_bv 64 (Z.shiftr u 26)) (Z_to_bv 64 0)) = true.
Proof.
  intros u Hu. unfold bv_eqb. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 26) with 67108864.
  assert (H1 : 1 <= u / 67108864 < 274877906944).
  { split; [apply Z.div_le_lower_bound; lia | apply Z.div_lt_upper_bound; lia]. }
  rewrite (unsigned_lit (u / 67108864)) by lia. change (bv_unsigned (Z_to_bv 64 0)) with 0.
  destruct (Z.eqb_spec (u / 67108864) 0); [lia | reflexivity].
Qed.

Lemma shr26_eq0 : forall u, 0 <= u < 67108864 ->
  negb (bv_eqb (Z_to_bv 64 (Z.shiftr u 26)) (Z_to_bv 64 0)) = false.
Proof.
  intros u Hu. unfold bv_eqb. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 26) with 67108864.
  rewrite Z.div_small by lia. reflexivity.
Qed.

(* The prologue 0x12c4c-0x12c80: sp := sp_h, the 13 saved registers at sp_h + 72. *)
Lemma ubs_pro_x :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (FR : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo sp_h : Z),
    sp = wz (sp_h + 176) -> mem_inv rsegs m -> stk rsegs m lo (sp_h + 176) -> lo <= sp_h + 72 ->
    evt rsegs
      (fun ms' => exists m' : word -> option byte,
         ms' = MS (mkR ra (wz sp_h) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                       t3 t4 t5 t6) FR (Z_to_bv 64 (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0x38)%Z)) fc None m' (seg_rom rsegs) /\
         munch [(sp_h + 72, sp_h + 176)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
         stk rsegs m' lo (sp_h + 176) /\
         rw_cells rsegs m' (sp_h + 72) (ubs_saved_cells ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          FR (Z_to_bv 64 (symaddr Symbols.Ubsan.s_LLVMFuzzerTestOneInput)) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    FR fc m lo sp_h HSP MI ST LO.
  subst sp. unfold wz.
  pose proof ST as (Hlo & Hhi & _).
  destruct (stk_carve rsegs m lo (sp_h + 176) 104 ST ltac:(lia)) as [_ [junk SV]].
  replace (sp_h + 176 - Z.of_nat 104) with (sp_h + 72) in SV by lia.
  pose proof (munch_refl [(sp_h + 72, sp_h + 176)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  do 14 step.
  apply evt_done. eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
  exact SV.
Qed.

(* E0: 0x12c4c with a payload of 2^26 bytes or more: the prologue, `srli`/`bnez` to 0x130d4, then R7. *)
Lemma ubs_E0_x :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (FR : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo sp_h z : Z),
    sp = wz (sp_h + 176) -> a1 = wz z -> 2 ^ 26 <= z < 2 ^ 64 ->
    mem_inv rsegs m -> stk rsegs m lo (sp_h + 176) -> lo <= sp_h ->
    evt rsegs
      (fun ms' => exists (a2' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz 0) a1 a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                       t3 t4 t5 t6) FR (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(sp_h + 72, sp_h + 176)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
         stk rsegs m' lo (sp_h + 176) /\
         rw_cells rsegs m' (sp_h + 72) (ubs_saved_cells ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          FR (Z_to_bv 64 (symaddr Symbols.Ubsan.s_LLVMFuzzerTestOneInput)) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    FR fc m lo sp_h z HSP HA1 HZ MI ST LO.
  pose proof ST as (Hlo & Hhi & _).
  eapply evt_cut; [eapply ubs_pro_x; [exact HSP | exact MI | exact ST | lia] | ].
  intros ms' (m1 & E & MU1 & WM1 & MI1 & ST1 & SV). subst ms' sp a1.
  assert (Uz : bv_unsigned (Z_to_bv 64 z) = z) by (apply unsigned_lit; lia).
  pose proof (rw_bytes _ _ _ SV) as SVB. rewrite ubs_saved_cells_bytes in SVB.
  unfold wz.
  step. step.
  lazymatch goal with |- context [Z.shiftr ?u 26] => if_true_by (shr26_ne0 u ltac:(lia)) end.
  eapply evt_mono.
  { eapply ubs_R7_x with (sp_h := sp_h); [apply unsigned_lit; lia | exact SVB]. }
  intros ms' E. cbv beta in E. subst ms'. do 2 eexists. split; [reflexivity|].
  split; [exact MU1|]. split; [exact WM1|]. split; [exact MI1|]. split; [exact ST1|]. exact SV.
Qed.

(* E: 0x12c4c with z < 2^26 to the malloc of the file copy (0x141ec, ra = 0x12cf0). n = length of the file
   (z - 1, or 0), c0 = the first payload byte (0 for an empty payload), P = the file pointer. *)
Lemma ubs_E_x :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (FR : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo sp_h p z n c0 P : Z) (d : byte)
         (vc v0 v1 : word),
    sp = wz (sp_h + 176) -> a0 = wz p -> a1 = wz z -> 0 <= z < 2 ^ 26 -> 0 < p -> p + z < 2 ^ 64 ->
    ((z = 0 /\ n = 0 /\ c0 = 0 /\ P = p) \/
     (1 <= z /\ n = z - 1 /\ c0 = bv_unsigned d /\ P = p + 1 /\ bytes_at rsegs m p [d] /\
      (p + z <= lo \/ sp_h + 176 <= p))) ->
    mem_inv rsegs m -> stk rsegs m lo (sp_h + 176) -> lo <= sp_h -> (symaddr Symbols.Ubsan.s_environ) <= lo ->
    rw_cells rsegs m sp_h [C8 vc] -> rw_cells rsegs m (symaddr Symbols.Ubsan.s_g_file_len) [C8 v0; C8 v1] ->
    evt rsegs
      (fun ms' => exists (a1' a2' : word) (m' : word -> option byte),
         ms' = MS (mkR (wz (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0xa4)%Z)) (wz sp_h) gp tp t0 t1 t2 s0 (wz P) (wz n) a1' a2' a3 a4 a5 a6 a7
                       (wz n) s3 s4 s5 s6 s7 s8 s9 (wz (symaddr Symbols.Ubsan.s_g_file_len)) s11 t3 t4 t5 t6)
                  FR (Z_to_bv 64 (symaddr Symbols.Ubsan.s_malloc)) fc None m' (seg_rom rsegs) /\
         munch [(sp_h, sp_h + 176); ((symaddr Symbols.Ubsan.s_g_file_len), (symaddr Symbols.Ubsan.s_environ))] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
         stk rsegs m' lo (sp_h + 176) /\
         bytes_at rsegs m' (sp_h + 72) (ubs_saved ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) /\
         rw_cells rsegs m' sp_h [C8 (wz c0)] /\ rw_cells rsegs m' (symaddr Symbols.Ubsan.s_g_file_len) [C8 (wz n); C8 (wz P)])
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          FR (Z_to_bv 64 (symaddr Symbols.Ubsan.s_LLVMFuzzerTestOneInput)) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    FR fc m lo sp_h p z n c0 P d vc v0 v1 HSP HA0 HA1 HZ HP0 HPZ HCASE MI ST LO LOG HC HG.
  subst sp a0 a1.
  pose proof ST as (Hlo & Hhi & _).
  pose proof (munch_refl [(sp_h, sp_h + 176); ((symaddr Symbols.Ubsan.s_g_file_len), (symaddr Symbols.Ubsan.s_environ))] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  destruct HCASE as [(Ez & En & Ec & EP) | (Hz1 & En & Ec & EP & HD & DJ)]; subst n c0 P.
  1: subst z.
  2: apply ba_ro1 in HD.
  all: eapply evt_cut; [eapply ubs_pro_x; [reflexivity | exact MI | exact ST | lia] | ].
  all: intros ms' (m1 & E & MU1 & WM1 & MI1 & ST1 & SV); subst ms'.
  all: transport_after_call rsegs m m1 MU1 WM1; clear MU1 WM1.
  all: unfold wz.
  (* z = 0 *)
  1: step; step; bres; step; step; bres; step; step; step.
  (* 1 <= z *)
  2: assert (Uz : bv_unsigned (Z_to_bv 64 z) = z) by (apply unsigned_lit; lia).
  2: step; step; lazymatch goal with |- context [Z.shiftr ?u 26] => if_false_by (shr26_eq0 u ltac:(lia)) end.
  2: step; step; bres; step; step; step; bres; step; step; step; step; step.
  (* both at 0x12cc0 *)
  all: step; step; step; step; step; bres.
  all: zstep; zstep; zstep; decide_tests; cbn [Z.b2z]; zstep; bres.
  all: step; step; step.
  all: apply evt_done; do 3 eexists; split; [reflexivity|].
  all: split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; [eassumption|].
  all: split; [pose proof (rw_bytes _ _ _ SV) as SVB; rewrite ubs_saved_cells_bytes in SVB; exact SVB|].
  all: split; eassumption.
Qed.

(* The 8-byte word at .rodata 0x103f8 that initializes the three words of ps. *)
Definition ubs_A5 : word := Z_to_bv 64 0xa5a5a5a5a5a5a5a5.

(* A: 0x12cf0 (a0 = b, the file copy block) to the call of pcap_source_open (0x1321c, ra = 0x12d38): the
   copy of the n file bytes from src to b (memcpy, when n <> 0), g_file := b, ps := three A5 words. *)
Lemma ubs_A_x :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (FR : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo sp_h b src n : Z)
         (F junk jps : list byte) (v8 : word),
    memcpy_contract ->
    bv_unsigned sp = sp_h -> a0 = wz b -> s1 = wz src -> s2 = wz n -> s10 = wz (symaddr Symbols.Ubsan.s_g_file_len) ->
    0 < b -> b + n < 2 ^ 63 -> Z.of_nat (length F) = n ->
    bytes_at rsegs m src F -> (src + n <= b \/ b + n <= src) ->
    rw_cells rsegs m b [CB (Z.to_nat n) junk] ->
    (b + n <= lo \/ sp_h + 176 <= b) -> (b + n <= (symaddr Symbols.Ubsan.s_g_file) \/ (symaddr Symbols.Ubsan.s_environ) <= b) ->
    mem_inv rsegs m -> stk rsegs m lo (sp_h + 176) -> lo <= sp_h -> (symaddr Symbols.Ubsan.s_environ) <= lo ->
    rw_cells rsegs m (sp_h + 48) [CB 24 jps] -> rw_cells rsegs m (symaddr Symbols.Ubsan.s_g_file) [C8 v8] ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR (wz (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0xec)%Z)) sp gp tp t0' t1' t2' (wz b) s1 (wz (sp_h + 48)) (wz (symaddr (Symbols.Ubsan.Sec.s_rodata + 0xe9)%Z)) a2' a3' a4' a5'
                       a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  FR (Z_to_bv 64 (symaddr Symbols.Ubsan.s_pcap_source_open)) fc None m' (seg_rom rsegs) /\
         munch [(sp_h + 48, sp_h + 72); (b, b + n); ((symaddr Symbols.Ubsan.s_g_file), (symaddr Symbols.Ubsan.s_environ))] m m' /\ wmono rsegs m m' /\
         mem_inv rsegs m' /\ stk rsegs m' lo (sp_h + 176) /\
         rw_cells rsegs m' b [CB (Z.to_nat n) F] /\ rw_cells rsegs m' (symaddr Symbols.Ubsan.s_g_file) [C8 (wz b)] /\
         rw_cells rsegs m' (sp_h + 48) [C8 ubs_A5; C8 ubs_A5; C8 ubs_A5])
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          FR (Z_to_bv 64 (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0xa4)%Z)) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    FR fc m lo sp_h b src n F junk jps v8 MEMC HSP HA0 HS1 HS2 HS10 Hb0 Hbn HLF HSRC DJS HJ DJK DJG MI ST LO LOG
    HPS HG8.
  subst sp_h a0 s1 s2 s10. unfold memcpy_contract in MEMC.
  pose proof ST as (Hlo & Hhi & _).
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  pose proof (munch_refl [(bv_unsigned sp + 48, bv_unsigned sp + 72); (b, b + n); ((symaddr Symbols.Ubsan.s_g_file), (symaddr Symbols.Ubsan.s_environ))] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  assert (Ub : bv_unsigned (Z_to_bv 64 b) = b) by (apply unsigned_lit; lia).
  assert (Un : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
  unfold wz.
  destruct (Z.eq_dec n 0) as [N0|N0].
  - (* n = 0: no copy *)
    rewrite N0 in *.
    assert (EF : F = []) by (destruct F; [reflexivity | cbn in HLF; lia]). subst F.
    pose proof (proj1 (proj1 HJ)) as WJ. cbn in WJ. destruct junk; [| cbn in WJ; lia].
    step. step. bres. step. bres.
    step. step. step. step. step. step. step. step. step. step.
    apply evt_done. do 14 eexists. split; [reflexivity|].
    split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
    split; [eassumption|]. split; eassumption.
  - (* n <> 0: memcpy (b, src, n) *)
    pose proof (bytes_at_bound rsegs _ _ _ HSRC) as BS.
    assert (Usrc : bv_unsigned (Z_to_bv 64 src) = src) by (apply unsigned_lit; lia).
    step. step. bres. step. bres. step. bres. step. step. step. step.
    eapply evt_cut; [eapply MEMC with (src := F) (junk := junk) | ].
    { rewrite Usrc. exact HSRC. }
    { rewrite Un, <- HLF, Nat2Z.id. reflexivity. }
    { rewrite Ub, Un. exact HJ. }
    { rewrite Ub, Usrc, Un. lia. }
    { exact MI. }
    intros ms' PO. unfold memcpy_post in PO.
    destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 &
                    E & MU1 & WM1 & MI1 & HB1 & HS1).
    subst ms'. rewrite Ub, Un in MU1, HB1. clear HS1.
    transport_after_call rsegs m m1 MU1 WM1. clear MU1 WM1.
    fix_ret.
    step. step. step. step. step. step. step. step. step. step.
    apply evt_done. do 14 eexists. split; [reflexivity|].
    split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
    split; [eassumption|]. split; eassumption.
Qed.

(* The magic test of the harness (0x12d44-0x12d94) and the byte order test (0x12dac-0x12dc0). check_1
   (rd32 at 0x131a8) returns the sign extension of rd_val; the code compares it with the sign-extended
   constants that `lui`/`addiw` build. *)

Lemma ubs_byte_range : forall c : byte, 0 <= bv_unsigned c < 256.
Proof. intros c. pose proof (bv_unsigned_in_range 8 c) as R. unfold bv_modulus in R. exact R. Qed.

(* rd_val with a1 = 0 of the first 4 bytes of the file is pcap_magic of the file. *)
Lemma ubs_rdval_magic : forall y0 y1 y2 y3 rest,
  rd_val (wz 0) y0 y1 y2 y3 = pcap_magic (y0 :: y1 :: y2 :: y3 :: rest).
Proof. intros. reflexivity. Qed.

Lemma ubs_magic_range : forall F, 0 <= pcap_magic F < 4294967296.
Proof.
  intros F. unfold pcap_magic, pcap_byte.
  pose proof (ubs_byte_range (nth 0 F (Z_to_bv 8 0))). pose proof (ubs_byte_range (nth 1 F (Z_to_bv 8 0))).
  pose proof (ubs_byte_range (nth 2 F (Z_to_bv 8 0))). pose proof (ubs_byte_range (nth 3 F (Z_to_bv 8 0))).
  lia.
Qed.

(* The unsigned value of the sign extension of a 32-bit value. *)
Lemma ubs_sx32_u : forall M, 0 <= M < 4294967296 ->
  bv_unsigned (wz (bv_swrap 32 M)) = if M <? 2147483648 then M else M + 18446744069414584320.
Proof.
  intros M HM. unfold wz. rewrite unsigned_lit_wrap. unfold bv_swrap, bv_wrap.
  change (bv_half_modulus 32) with 2147483648. change (bv_modulus 32) with 4294967296.
  change (2 ^ 64) with 18446744073709551616.
  destruct (Z.ltb_spec M 2147483648); cbv iota.
  - rewrite (Z.mod_small (M + 2147483648) 4294967296) by lia.
    replace (M + 2147483648 - 2147483648) with M by lia. apply Z.mod_small. lia.
  - rewrite <- (Z.mod_unique (M + 2147483648) 4294967296 1 (M - 2147483648)) by lia.
    rewrite <- (Z.mod_unique (M - 2147483648 - 2147483648) 18446744073709551616 (-1)
                  (M + 18446744069414584320)) by lia.
    reflexivity.
Qed.

(* The sign-extended forms agree exactly when the 32-bit values agree. *)
Lemma ubs_sx32_inj : forall M K, 0 <= M < 4294967296 -> 0 <= K < 4294967296 ->
  (bv_unsigned (wz (bv_swrap 32 M)) = bv_unsigned (wz (bv_swrap 32 K)) <-> M = K).
Proof.
  intros M K HM HK. rewrite !ubs_sx32_u by lia. split; [|intros ->; reflexivity].
  destruct (Z.ltb_spec M 2147483648), (Z.ltb_spec K 2147483648); lia.
Qed.

(* The constants of `lui a2,0xa1b2c; addiw a2,a2,980` and `lui a3,0xd4c3b; addiw a3,a3,673`. *)
Lemma ubs_K1_val : Z_to_bv 64 (-1582119980) = wz (bv_swrap 32 0xA1B2C3D4).
Proof. apply bv_eq. vm_compute. reflexivity. Qed.
Lemma ubs_K2_val : Z_to_bv 64 (-725372255) = wz (bv_swrap 32 0xD4C3B2A1).
Proof. apply bv_eq. vm_compute. reflexivity. Qed.

(* check_1's answer (the sign extension of rd_val (wz 0) of the first 4 file bytes) is the sign extension of a
   32-bit constant K exactly when pcap_magic of the file is K. *)
Lemma ubs_magic_sx : forall y0 y1 y2 y3 rest K, 0 <= K < 4294967296 ->
  (wz (bv_swrap 32 (rd_val (wz 0) y0 y1 y2 y3)) = wz (bv_swrap 32 K) <->
   pcap_magic (y0 :: y1 :: y2 :: y3 :: rest) = K).
Proof.
  intros y0 y1 y2 y3 rest K HK. rewrite (ubs_rdval_magic y0 y1 y2 y3 rest).
  pose proof (ubs_magic_range (y0 :: y1 :: y2 :: y3 :: rest)) as R.
  split.
  - intros E. apply (f_equal bv_unsigned) in E. exact (proj1 (ubs_sx32_inj _ _ R HK) E).
  - intros E. rewrite E. reflexivity.
Qed.

Lemma ubs_sx32_ne : forall M k, 0 <= M < 4294967296 -> M <> k -> M + 18446744069414584320 <> k ->
  bv_unsigned (Z_to_bv 64 (bv_swrap 32 M)) <> k.
Proof.
  intros M k HM H1 H2. change (Z_to_bv 64 (bv_swrap 32 M)) with (wz (bv_swrap 32 M)).
  rewrite ubs_sx32_u by lia. destruct (M <? 2147483648); assumption.
Qed.

Lemma ubs_snez_lxor : forall (w : word) k, 0 <= k < 18446744073709551616 -> bv_unsigned w <> k ->
  v_sltu (Z_to_bv 64 0) (Z_to_bv 64 (Z.lxor (bv_unsigned w) k)) = Z_to_bv 64 1.
Proof.
  intros w k Hk Hne. unfold v_sltu, c_ltu, bv_ltu.
  assert (L : inr64 (Z.lxor (bv_unsigned w) k)) by (apply zr_lxor; [apply zr_word | unfold inr64; lia]).
  unfold inr64 in L. rewrite (unsigned_lit (Z.lxor (bv_unsigned w) k)) by exact L.
  change (bv_unsigned (Z_to_bv 64 0)) with 0.
  assert (Z.lxor (bv_unsigned w) k <> 0) by (intro E; apply Z.lxor_eq in E; contradiction).
  destruct (Z.ltb_spec 0 (Z.lxor (bv_unsigned w) k)); [reflexivity | exfalso; lia].
Qed.

Lemma ubs_sltiu : forall n k, 0 <= n < 18446744073709551616 -> 0 <= k < 18446744073709551616 ->
  v_sltiu (Z_to_bv 64 n) k = Z_to_bv 64 (Z.b2z (n <? k)).
Proof.
  intros n k Hn Hk. unfold v_sltiu. rewrite unsigned_lit by lia. unfold bv_wrap.
  change (bv_modulus 64) with 18446744073709551616. rewrite (Z.mod_small k) by lia.
  destruct (n <? k); reflexivity.
Qed.

Lemma ubs_slli3 : forall c, 0 <= c < 256 -> Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 c)) 3) = Z_to_bv 64 (8 * c).
Proof. intros c Hc. rewrite unsigned_lit by lia. rewrite Z.shiftl_mul_pow2 by lia. f_equal. lia. Qed.

Lemma ubs_good_eq : forall F, pcap_good F =
  (24 <=? Z.of_nat (length F)) && ((pcap_magic F =? 0xA1B2C3D4) || (pcap_magic F =? 0xD4C3B2A1)).
Proof. reflexivity. Qed.

(* After `snez`: the value is 0 or 1, by computation when it is closed, or 1 when the xor operand is not the
   constant. *)
Ltac snez_fix k :=
  let v := get_reg k in
  first [ assert_fails (idtac; match v with context [?x] => is_var x end);
          first [ replace v with (Z_to_bv 64 0) by (apply bv_eq; vm_compute; reflexivity)
                | replace v with (Z_to_bv 64 1) by (apply bv_eq; vm_compute; reflexivity) ]
        | replace v with (Z_to_bv 64 1)
            by (symmetry; apply ubs_snez_lxor; [lia | apply ubs_sx32_ne; lia])
        | idtac "snez_fix failed:" v; fail 1 ].

(* Refused file: 0x12d9c with s1 = -1 and the f cell of ps 0, to free(b) (0x140ac, ra = 0x130d4). *)
Lemma ubs_B_ref :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (FR : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (b : Z),
    s0 = wz b -> s1 = wz (-1) -> ro_cells rsegs m (bv_unsigned sp + 48) [C8 (Z_to_bv 64 0)] ->
    evt rsegs
      (fun ms' => ms' = MS (mkR (wz (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0x488)%Z)) sp gp tp t0 t1 t2 s0 s1 (wz b) a1 a2 a3 a4 a5 a6 a7
                                s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) FR (Z_to_bv 64 (symaddr Symbols.Ubsan.s_free)) fc None m
                           (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          FR (Z_to_bv 64 (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0x150)%Z)) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    FR fc m b HS0 HS1 HF.
  subst s0 s1. unfold wz.
  step. bres. step. step. bres. step. step.
  apply evt_done. reflexivity.
Qed.

(* Good file: 0x12d9c with s1 = 0 and a0 = the sign extension of the magic K (0xa1b2c3d4 or 0xd4c3b2a1), to
   malloc(max (8 c0) 1) (0x141ec, ra = 0x12ddc). *)
Lemma ubs_B_good :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (FR : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (K sw c0 : Z),
    s1 = wz 0 -> a0 = wz (bv_swrap 32 K) -> (K = 0xA1B2C3D4 \/ K = 0xD4C3B2A1) ->
    sw = (if K =? 0xD4C3B2A1 then 1 else 0) ->
    ro_cells rsegs m (bv_unsigned sp + 56) [C4 (Z_to_bv 64 sw)] ->
    ro_cells rsegs m (bv_unsigned sp) [C8 (Z_to_bv 64 c0)] -> 0 <= c0 < 256 ->
    evt rsegs
      (fun ms' => exists (a1' a2' a3' : word),
         ms' = MS (mkR (wz (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0x190)%Z)) sp gp tp t0 t1 t2 s0 (wz (8 * c0)) (wz (Z.max (8 * c0) 1)) a1' a2' a3' a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) FR (Z_to_bv 64 (symaddr Symbols.Ubsan.s_malloc)) fc None m
                  (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          FR (Z_to_bv 64 (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0x150)%Z)) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    FR fc m K sw c0 HS1 HA0 HK Hsw HSW HC Hc.
  subst s1 a0. unfold wz.
  assert (Uc : bv_unsigned (Z_to_bv 64 c0) = c0) by (apply unsigned_lit; lia).
  destruct HK as [-> | ->]; cbn in Hsw; subst sw.
  all: step; bres; step; step; step; step; step; step; bres; step; step.
  all: rep_reg 9 (Z_to_bv 64 (8 * c0)) ltac:(symmetry; apply ubs_slli3; lia).
  all: step; destruct (Z.eq_dec c0 0) as [C0|C0].
  1,3: subst c0; step; bres; step; step; apply evt_done; do 3 eexists; reflexivity.
  all: step; bres; step; rewrite Z.max_l by lia; apply evt_done; do 3 eexists; reflexivity.
Qed.

(* B: 0x12d38 (a0 = r, the answer of pcap_source_open) to malloc of the record buffer (good file) or to
   free(b) (refused file). The harness's magic (0 when n < 4, else check_1 (b, 0)) and the tests at 0x12d98
   and 0x12dc0 agree with pcap_good and pcap_sw. *)
Lemma ubs_B_x :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (FR : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (sp_h b n c0 cap r : Z) (F : list byte),
    rd32f_contract ->
    bv_unsigned sp = sp_h -> a0 = wz r -> s0 = wz b -> s10 = wz (symaddr Symbols.Ubsan.s_g_file_len) ->
    bytes_at rsegs m (symaddr Symbols.Ubsan.s_g_file_len) (le8 (wz n)) -> Z.of_nat (length F) = n -> bytes_at rsegs m b F ->
    0 < b -> b + n < 2 ^ 63 ->
    bytes_at rsegs m sp_h (le8 (wz c0)) -> 0 <= c0 < 256 -> cap = 8 * c0 ->
    r = (if pcap_good F then 0 else -1) ->
    (pcap_good F = true -> bytes_at rsegs m (sp_h + 56) (le4 (wz (pcap_sw F)))) ->
    (pcap_good F = false -> bytes_at rsegs m (sp_h + 48) (le8 (wz 0))) ->
    evt rsegs
      (fun ms' =>
         (pcap_good F = true /\ exists (a1' a2' a3' a4' a5' : word),
            ms' = MS (mkR (wz (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0x190)%Z)) sp gp tp t0 t1 t2 s0 (wz cap) (wz (Z.max cap 1)) a1' a2' a3' a4' a5' a6 a7
                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) FR (Z_to_bv 64 (symaddr Symbols.Ubsan.s_malloc)) fc None m
                     (seg_rom rsegs)) \/
         (pcap_good F = false /\ exists (a1' a2' a3' a4' a5' : word),
            ms' = MS (mkR (wz (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0x488)%Z)) sp gp tp t0 t1 t2 s0 (wz (-1)) (wz b) a1' a2' a3' a4' a5' a6 a7
                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) FR (Z_to_bv 64 (symaddr Symbols.Ubsan.s_free)) fc None m
                     (seg_rom rsegs)))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          FR (Z_to_bv 64 (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0xec)%Z)) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    FR fc m sp_h b n c0 cap r F RD HSP HA0 HS0 HS10 HNB HLF HFB Hb0 Hbn HCB Hc0 Hcap Hr HG1 HG0.
  unfold rd32f_contract, RD32F in RD.
  subst sp_h a0 s0 s10 cap.
  apply ba_ro8 in HNB. apply ba_ro8 in HCB. unfold wz in *.
  assert (Ub : bv_unsigned (Z_to_bv 64 b) = b) by (apply unsigned_lit; lia).
  assert (Un : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
  destruct (Z.ltb_spec n 4) as [N4|N4].
  - (* n < 4: magic 0, the length test fails *)
    assert (G : pcap_good F = false).
    { rewrite ubs_good_eq, HLF. destruct (Z.leb_spec 24 n); [exfalso; lia | reflexivity]. }
    rewrite G in Hr |- *. cbv iota in Hr. subst r.
    specialize (HG0 G). apply ba_ro8 in HG0. clear HG1.
    step. step. step. step. bres. step. step.
    do 7 step. snez_fix 12. step. snez_fix 13. do 4 step. step. bres.
    eapply evt_mono; [eapply ubs_B_ref; [reflexivity | reflexivity | exact HG0] | ].
    intros ms' E. right. split; [reflexivity|]. do 5 eexists. exact E.
  - (* n >= 4: magic = check_1 (b, 0) = pcap_magic F *)
    destruct F as [|y0 [|y1 [|y2 [|y3 rest]]]]; try (cbn [length] in HLF; lia).
    assert (HB4 : bytes_at rsegs m b [y0; y1; y2; y3]).
    { change (y0 :: y1 :: y2 :: y3 :: rest) with ([y0; y1; y2; y3] ++ rest) in HFB.
      apply bytes_at_app in HFB. exact (proj1 HFB). }
    remember (pcap_magic (y0 :: y1 :: y2 :: y3 :: rest)) as M eqn:HM.
    pose proof (ubs_magic_range (y0 :: y1 :: y2 :: y3 :: rest)) as MR. rewrite <- HM in MR.
    assert (HB4' : bytes_at rsegs m (bv_unsigned (Z_to_bv 64 b)) [y0; y1; y2; y3]) by (rewrite Ub; exact HB4).
    step. step. step. step. bres. step. step. step.
    eapply evt_cut; [eapply RD | ].
    { rewrite Ub. lia. }
    { exact HB4'. }
    intros ms' (a1' & a2' & a3' & a4' & a5' & E). subst ms'.
    replace (rd_val (Z_to_bv 64 0) y0 y1 y2 y3) with (pcap_magic (y0 :: y1 :: y2 :: y3 :: rest))
      by (symmetry; exact (ubs_rdval_magic y0 y1 y2 y3 rest)).
    rewrite <- HM.
    fix_ret. unfold wz.
    step. step.
    rep_reg 11 (Z_to_bv 64 (Z.b2z (n <? 24))) ltac:(first [apply ubs_sltiu | symmetry; apply ubs_sltiu]; lia).
    step.
    destruct (Z.eqb_spec M 0xA1B2C3D4) as [EK|NK1];
      [rewrite EK | destruct (Z.eqb_spec M 0xD4C3B2A1) as [EK|NK2]; [rewrite EK | ]].
    all: destruct (Z.ltb_spec n 24) as [N24|N24]; cbn [Z.b2z].
    all: do 7 step; snez_fix 12; step; snez_fix 13; do 4 step; step.
    (* pcap_good of the file in each case: K1 or K2 with n >= 24 is good, the others are refused *)
    all: first [ assert (G : pcap_good (y0 :: y1 :: y2 :: y3 :: rest) = true)
                   by (rewrite ubs_good_eq, <- HM, HLF; destruct (Z.leb_spec 24 n);
                       destruct (Z.eqb_spec M 0xA1B2C3D4); destruct (Z.eqb_spec M 0xD4C3B2A1);
                       cbn [andb orb]; first [reflexivity | exfalso; lia])
               | assert (G : pcap_good (y0 :: y1 :: y2 :: y3 :: rest) = false)
                   by (rewrite ubs_good_eq, <- HM, HLF; destruct (Z.leb_spec 24 n);
                       destruct (Z.eqb_spec M 0xA1B2C3D4); destruct (Z.eqb_spec M 0xD4C3B2A1);
                       cbn [andb orb]; first [reflexivity | exfalso; lia]) ].
    all: rewrite G in Hr |- *; cbv iota in Hr; subst r; bres.
    all: lazymatch type of G with
         | _ = true =>
             specialize (HG1 G); apply ba_ro4 in HG1; clear HG0;
             eapply evt_mono;
             [ eapply ubs_B_good with (K := M) (sw := pcap_sw (y0 :: y1 :: y2 :: y3 :: rest));
               [ reflexivity | rewrite EK; reflexivity | rewrite EK; first [left; reflexivity | right; reflexivity]
               | unfold pcap_sw; rewrite <- HM; reflexivity | exact HG1 | exact HCB | lia ]
             | intros ms' (a1'' & a2'' & a3'' & E); left; split; [reflexivity|];
               exists a1'', a2'', a3'', a4', a5'; exact E ]
         | _ = false =>
             specialize (HG0 G); apply ba_ro8 in HG0; clear HG1;
             eapply evt_mono; [eapply ubs_B_ref; [reflexivity | reflexivity | exact HG0] | ];
             intros ms' E; right; split; [reflexivity|]; do 5 eexists; exact E
         end.
Qed.

(* C: 0x12ddc (a0 = buf, the record buffer) to the first call of pcap_source_next (0x13318, ra = 0x12e04):
   buf at sp_h + 24, ts := -1 at sp_h + 40, s2 := buf. *)
Lemma ubs_C_x :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (FR : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo sp_h buf cap : Z) (v24 v40 : word),
    bv_unsigned sp = sp_h -> a0 = wz buf -> 0 < buf < 2 ^ 64 -> s1 = wz cap ->
    mem_inv rsegs m -> stk rsegs m lo (sp_h + 176) -> lo <= sp_h ->
    rw_cells rsegs m (sp_h + 24) [C8 v24] -> rw_cells rsegs m (sp_h + 40) [C8 v40] ->
    evt rsegs
      (fun ms' => exists m' : word -> option byte,
         ms' = MS (mkR (wz (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0x1b8)%Z)) sp gp tp t0 t1 t2 s0 s1 (wz (sp_h + 48)) (wz buf) (wz cap) (wz (sp_h + 40))
                       a4 a5 a6 a7 (wz buf) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  FR (Z_to_bv 64 (symaddr Symbols.Ubsan.s_pcap_source_next)) fc None m' (seg_rom rsegs) /\
         munch [(sp_h + 24, sp_h + 32); (sp_h + 40, sp_h + 48)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
         stk rsegs m' lo (sp_h + 176) /\
         rw_cells rsegs m' (sp_h + 24) [C8 (wz buf)] /\ rw_cells rsegs m' (sp_h + 40) [C8 (wz (-1))])
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          FR (Z_to_bv 64 (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0x190)%Z)) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    FR fc m lo sp_h buf cap v24 v40 HSP HA0 HB HS1 MI ST LO H24 H40.
  subst sp_h a0 s1.
  pose proof ST as (Hlo & Hhi & _).
  pose proof (munch_refl [(bv_unsigned sp + 24, bv_unsigned sp + 32); (bv_unsigned sp + 40, bv_unsigned sp + 48)] m)
    as MU.
  pose proof (wmono_refl rsegs m) as WM.
  assert (Ub : bv_unsigned (Z_to_bv 64 buf) = buf) by (apply unsigned_lit; lia).
  unfold wz.
  step. step. bres. step. step. step. step. step. step. step. step.
  apply evt_done. eexists. split; [reflexivity|].
  split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
  split; eassumption.
Qed.
