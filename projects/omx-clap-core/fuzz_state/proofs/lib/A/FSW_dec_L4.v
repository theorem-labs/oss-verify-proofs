(* preset_base64_decode (fs.asan 0x8481c), part L4 of the Theorem Labs lane walk (a Theorem Labs lane), helper a Theorem Labs lane:
   one loop iteration on a base64 letter or any other byte that is not whitespace, not '=' and not the NUL. From the head
   0x848bc through `memchr (g_b64, c, 65)` to either the next head (the sextet taken, at most one byte stored at q + n)
   or the call of fuzz_free (memchr found nothing, or a letter after '='). Contract: (internal path) (statement
   of decL_arm_other verbatim). SCRATCH part (owner a Theorem Labs lane); a Theorem Labs lane integrates it.
   MEASURED with the token engine over FSW_writer_tbl.fsw_wr_tbl (scratch FSW_dec_L4m.v in the VM workspace, removed):
   - from decL_hss: the run stops at 0x848d0 `bltu s9, c` (two token atoms 48, 49); taken (61 < c) it reaches PC_memchr;
     not taken it stops at 0x848dc (the whitespace test), 0x848e0 (c <> 61), 0x848ec (c = 0) and then reaches PC_memchr;
     at PC_memchr ra = 0x848fc, a0 = s3 (atom 19), a1 = c (atom 47), a2 = 65, every other register its atom
     (decLO_cregs), the regions those of decL_hss;
   - from decL_mss: `beqz r` at 0x848fc (taken -> A_fuzz_free, decLO_fregs); not taken: stops at 0x84900 `bnez s10`
     (taken -> A_fuzz_free); not taken, with an atom fact on s8 (bits): bits = 0 -> DEC_HEAD with no store
     (decLO_hregs0); bits in [2, 6] -> DEC_HEAD with the byte `srlw(acc', bits - 2)` stored at atom 47 (decLO_hregs2,
     decLO_str2). The accumulator the engine computes is decLO_acc_e = (r - s3)_w | (s7 <<w 6), not FSW_dec_L2's
     decLA_acc_e: decLO_acc is its value lemma. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import
AB1v AB1w FSupoison FSupoisonU FSH_YC20 FSH_Gen FSH_Base FSH_Rt FSPstat FSH_Fn_alloc FSH_Fn_writer
FSW_K FSW_ret FSW_rres FSW_writer_tbl FSW_writer_model.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSW_dec_defs FSW_dec_L0 FSW_dec_L1 FSW_dec_L2 FSW_dec_L3.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require WriterSpec WriterSpecFacts.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ---- the engine's states at the cuts of this arm (MEASURED, see the header) ---- *)
(* at PC_memchr: ra = 0x848fc, a0 = s3, a1 = c, a2 = 65 *)
Definition decLO_cregs : list sv :=
  [SLit 0; SLit 542972; SOff 2 0; SOff 3 0; SOff 4 0; SOff 5 0; SOff 6 0; SOff 7 0; SOff 8 0; SOff 9 0;
   SOff 19 0; SOff 47 0; SLit 65; SOff 13 0; SOff 14 0; SOff 15 0; SOff 16 0; SOff 17 0;
   SOff 18 0; SOff 19 0; SOff 20 0; SOff 21 0; SOff 22 0; SOff 23 0; SOff 24 0; SOff 25 0; SOff 26 0; SOff 27 0;
   SOff 28 0; SOff 29 0; SOff 30 0; SOff 31 0].
(* at A_fuzz_free: ra = 0x8497c, a0 = s1 = q *)
Definition decLO_fregs : list sv :=
  [SLit 0; SLit 543100; SOff 2 0; SOff 3 0; SOff 4 0; SOff 5 0; SOff 6 0; SOff 7 0; SOff 8 0; SOff 9 0;
   SOff 9 0; SOff 11 0; SOff 12 0; SOff 13 0; SOff 14 0; SOff 15 0; SOff 16 0; SOff 17 0;
   SOff 18 0; SOff 19 0; SOff 20 0; SOff 21 0; SOff 22 0; SOff 23 0; SOff 24 0; SOff 25 0; SOff 26 0; SOff 27 0;
   SOff 28 0; SOff 29 0; SOff 30 0; SOff 31 0].
(* the accumulator: `subw a0, a0, s3; slliw a1, s7, 6; or s7, a0, a1` *)
Definition decLO_acc_e : sv :=
  SAlu ALU_OR (SAluw ALU_SUB (SOff 10 0) (SOff 19 0)) (SAluw ALU_SLL (SOff 23 0) (SLit 6)).
(* the next head, bits = 0: no store, s8 + 6 *)
Definition decLO_hregs0 : list sv :=
  [SLit 0; SOff 1 0; SOff 2 0; SOff 3 0; SOff 4 0; SOff 5 0; SOff 6 0; SOff 7 0; SOff 8 0; SOff 9 0;
   SAluw ALU_SUB (SOff 10 0) (SOff 19 0); SAluw ALU_SLL (SOff 23 0) (SLit 6); SOff 12 0; SOff 13 0; SOff 14 0;
   SOff 15 0; SOff 16 0; SOff 17 0;
   SOff 18 1; SOff 19 0; SOff 20 1; SOff 21 0; SOff 22 0; decLO_acc_e; SOff 24 6; SOff 25 0; SLit 0; SOff 27 0;
   SOff 28 0; SOff 29 0; SOff 30 0; SOff 31 0].
(* the next head, bits in [2, 6]: the byte srlw(acc', bits - 2) stored at q + n, s6 + 1, s8 - 2 *)
Definition decLO_hregs2 : list sv :=
  [SLit 0; SOff 1 0; SOff 2 0; SOff 3 0; SOff 4 0; SOff 5 0; SOff 6 0; SOff 7 0; SOff 8 0; SOff 9 0;
   SOff 47 0; SAluw ALU_SRL decLO_acc_e (SOff 24 (-2)); SOff 49 0; SOff 13 0; SOff 14 0; SOff 15 0; SOff 16 0;
   SOff 17 0;
   SOff 18 1; SOff 19 0; SOff 20 1; SOff 21 0; SOff 22 1; decLO_acc_e; SOff 24 (-2); SOff 25 0; SLit 0; SOff 27 0;
   SOff 28 0; SOff 29 0; SOff 30 0; SOff 31 0].
Definition decLO_str2 : YP09.region :=
  YP09.mkRegion (Some 47%nat) 0 1 0 1 [YP09.mkChunk 0 (CVal 1 (SAluw ALU_SRL decLO_acc_e (SOff 24 (-2))))].
(* the registers this arm keeps from the head (callee-saved, so also across memchr) *)
Definition decLO_kregs : list (bv 5) := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.

Ltac decLO_in := cbv [decLO_kregs In]; repeat (first [left; reflexivity | right]).
Ltac decLO_cs := unfold acallee_saved;
  lazymatch goal with |- context [bv_unsigned ?q] =>
    let z := eval vm_compute in (bv_unsigned q) in change (bv_unsigned q) with z end; lia.

(* ---- pure lemmas ---- *)
Lemma decLO_acc : forall E acc v, ew E 10 = Z_to_bv 64 (G_B64 + v) -> 0 <= v < 64 -> ew E 19 = Z_to_bv 64 G_B64 ->
  ew E 23 = Z_to_bv 64 acc -> 0 <= acc < 2 ^ 64 ->
  U E decLO_acc_e mod 4096 = (acc mod 64) * 64 + v.
Proof.
  intros E acc v H10 Hv H19 H23 Hacc. unfold decLO_acc_e.
  assert (UA : U E (SAluw ALU_SUB (SOff 10 0) (SOff 19 0)) = v).
  { rewrite (YP0e.U_of_S E (SAluw _ _ _)), YP0e.S_SAluw. cbn [zalu_raw].
    rewrite (YI04.U_atom E 10 (G_B64 + v) H10) by (unfold G_B64; lia).
    rewrite (YI04.U_atom E 19 G_B64 H19) by (unfold G_B64; lia).
    rewrite (Z.mod_small (G_B64 + v) (2 ^ 32)) by (unfold G_B64; lia).
    rewrite (Z.mod_small G_B64 (2 ^ 32)) by (unfold G_B64; lia).
    replace (G_B64 + v - G_B64) with v by ring.
    unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2 ^ 31).
    change (bv_modulus 32) with (2 ^ 32). change (bv_modulus 64) with (2 ^ 64).
    rewrite (Z.mod_small (v + 2 ^ 31) (2 ^ 32)) by lia.
    replace (v + 2 ^ 31 - 2 ^ 31) with v by ring. apply Z.mod_small. lia. }
  assert (HS : 0 <= U E (SAluw ALU_SLL (SOff 23 0) (SLit 6)) < 2 ^ 64 /\
    U E (SAluw ALU_SLL (SOff 23 0) (SLit 6)) mod 64 = 0 /\
    U E (SAluw ALU_SLL (SOff 23 0) (SLit 6)) mod 4096 = (acc mod 64) * 64).
  { rewrite (YP0e.U_of_S E (SAluw _ _ _)), YP0e.S_SAluw. cbn [zalu_raw].
    rewrite (YI04.U_atom E 23 acc H23 Hacc), YP0e.U_SLit.
    change (Z.land (zcanon 6 mod 2 ^ 32) 31) with 6. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 6) with 64.
    unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2 ^ 31).
    change (bv_modulus 32) with (2 ^ 32). change (bv_modulus 64) with (2 ^ 64).
    split; [|split]; Z.div_mod_to_equations; lia. }
  destruct HS as (HS1 & HS2 & HS3).
  rewrite YP0e.U_SAlu. cbn [zalu_raw]. rewrite UA.
  remember (U E (SAluw ALU_SLL (SOff 23 0) (SLit 6))) as US eqn:HUS.
  rewrite decLA_lor_add64 by lia.
  assert (HS4 : US <= 2 ^ 64 - 64) by (Z.div_mod_to_equations; lia).
  rewrite (YP0m.zcanon_small (v + US)) by lia.
  Z.div_mod_to_equations; lia.
Qed.

(* the low byte of any word *)
Lemma decLO_byteW : forall w : word, bv_unsigned (byte_of_word w 0) = bv_unsigned w mod 256.
Proof.
  intros w. unfold byte_of_word. rewrite Z.mul_0_r, Z.shiftr_0_r, Z_to_bv_unsigned.
  unfold bv_wrap. reflexivity.
Qed.
(* a one-byte CVal chunk's byte, with sv_denot kept folded (cbn would unfold it) *)
Lemma decLO_cbyte0 : forall E a e, YP09.cbyte tfibsegs E a (CVal 1 e) 0 = Some (byte_of_word (sv_denot E e) 0).
Proof. reflexivity. Qed.
(* the stored byte of the decLO_str2 region, as an aview value *)
Lemma decLO_str2_aview : forall E (H : word -> bool) (m : word -> option byte),
  region_ok tfibsegs E (mrestrict H m) decLO_str2 ->
  aview tfibsegs H m (bv_unsigned (ew E 47))
    = Some (U E (SAluw ALU_SRL decLO_acc_e (SOff 24 (-2))) mod 256).
Proof.
  intros E H m (_ & _ & _ & HC).
  cbv [decLO_str2 YP09.r_chunks YP09.r_base base_val] in HC.
  pose proof (Forall_inv HC) as Hck.
  destruct (Hck 0 ltac:(cbn; lia)) as (bb & Hcb & Hmb).
  cbv [YP09.c_off YP09.c_val] in Hcb, Hmb.
  rewrite !Z.add_0_r in Hmb.
  unfold aview. rewrite Hmb. cbv [option_map]. f_equal.
  rewrite decLO_cbyte0 in Hcb. injection Hcb as <-.
  rewrite decLO_byteW. reflexivity.
Qed.

(* memchr (g_b64, c, 65) reads at most the 65 table bytes and at least one *)
Lemma decLO_mchr : forall c, 0 <= c < 256 -> 1 <= mchr_len c WriterSpec.b64_table <= 65.
Proof.
  intros c Hc.
  pose proof (decLA_fin (fun c => (1 <=? mchr_len c WriterSpec.b64_table) && (mchr_len c WriterSpec.b64_table <=? 65))
    0 256 ltac:(vm_compute; reflexivity) c ltac:(lia)) as A.
  cbv beta in A. apply andb_prop in A as [A1 A2]. apply Z.leb_le in A1, A2. lia.
Qed.

(* a shadow hull visible over n bytes is visible over any shorter nonempty prefix *)
Lemma decLO_hull_sub : forall rd x n m, 1 <= m <= n -> shadow_hull_vis rd x n -> shadow_hull_vis rd x m.
Proof.
  intros rd x n m Hm H s Hs. apply H. unfold shadow_addr in *.
  assert (A1 : (x + m - 1) / 8 <= (x + n - 1) / 8) by (apply Z.div_le_mono; lia).
  assert (A2 : (SHADOW_OFF + (x + m - 1) / 8) / 8 <= (SHADOW_OFF + (x + n - 1) / 8) / 8) by (apply Z.div_le_mono; lia).
  lia.
Qed.

(* ---- the write windows of this arm's runs: the loop's frame [sp - 112, sp) and, after memchr, the byte q + n ---- *)
Lemma decLO_awr_h : forall B Ex d rs FP bl0 blc ly own fr0,
  bv_unsigned (ew Ex 2) = d_sp d - DEC_F -> d_sp d <= d_ot d ->
  rs = fsT_ret_regions DEC_F decL_cs [decL_txr] ->
  awr_ok tfibsegs B Ex rs (d_STKJ d) (d_ot d) FP bl0 blc ly own fr0.
Proof.
  intros B Ex d rs FP bl0 blc ly own fr0 E2 Hot ->.
  assert (FS : STK_preset_base64_decode = ltac:(let v := eval vm_compute in STK_preset_base64_decode in exact v)) by reflexivity.
  unfold fsT_ret_regions. cbn [app].
  eapply awr_ok_cons_stack_off with (n := 2%nat) (d := d_sp d - DEC_F - d_ot d);
    [reflexivity | rewrite E2; lia | cbv [fstk_ret YP09.r_wlo]; unfold d_STKJ, DEC_F; rewrite FS; lia
    | cbv [fstk_ret YP09.r_whi]; unfold DEC_F; lia |].
  apply awr_ok_cons_ro; [cbv [fs_got_region YP09.r_wlo YP09.r_whi]; lia|].
  apply awr_ok_cons_ro; [cbv [fs_bcell_region YP09.r_wlo YP09.r_whi]; lia|].
  apply awr_ok_cons_ro; [cbv [decL_txr YP09.r_wlo YP09.r_whi]; lia|].
  apply awr_ok_nil.
Qed.

Lemma decLO_awr_m : forall B Ex d rs p FP bl0 blc ly own fr0,
  bv_unsigned (ew Ex 2) = d_sp d - DEC_F -> bv_unsigned (ew Ex 47) = p -> d_sp d <= d_ot d ->
  in_tmp_block bl0 blc p ->
  rs = fsT_ret_regions DEC_F decL_cs [decL_str] ->
  awr_ok tfibsegs B Ex rs (d_STKJ d) (d_ot d) FP bl0 blc ly own fr0.
Proof.
  intros B Ex d rs p FP bl0 blc ly own fr0 E2 E47 Hot Htmp ->.
  assert (FS : STK_preset_base64_decode = ltac:(let v := eval vm_compute in STK_preset_base64_decode in exact v)) by reflexivity.
  unfold fsT_ret_regions. cbn [app].
  eapply awr_ok_cons_stack_off with (n := 2%nat) (d := d_sp d - DEC_F - d_ot d);
    [reflexivity | rewrite E2; lia | cbv [fstk_ret YP09.r_wlo]; unfold d_STKJ, DEC_F; rewrite FS; lia
    | cbv [fstk_ret YP09.r_whi]; unfold DEC_F; lia |].
  apply awr_ok_cons_ro; [cbv [fs_got_region YP09.r_wlo YP09.r_whi]; lia|].
  apply awr_ok_cons_ro; [cbv [fs_bcell_region YP09.r_wlo YP09.r_whi]; lia|].
  eapply awr_ok_cons_gen with (k := 47%nat) (b := p); [reflexivity | exact E47 | | apply awr_ok_nil].
  intros a Ha. cbv [decL_str YP09.r_wlo YP09.r_whi] in Ha. replace a with p by lia.
  left. right. right. left. exact Htmp.
Qed.

(* the memory a run leaves: the bytes outside its write windows are those it started from (the frame first, so that
   the env and the regions are fixed before the side goals are elaborated) *)
Lemma decLO_meq_h : forall Ex d rs (m0 m1 m2 : word -> option byte),
  frame_of Ex rs m1 m2 -> bv_unsigned (ew Ex 2) = d_sp d - DEC_F ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (d_sp d - DEC_F <= a < d_sp d) -> m1 (Z_to_bv 64 a) = m0 (Z_to_bv 64 a)) ->
  rs = fsT_ret_regions DEC_F decL_cs [decL_txr] ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (d_sp d - DEC_F <= a < d_sp d) -> m2 (Z_to_bv 64 a) = m0 (Z_to_bv 64 a)).
Proof.
  intros Ex d rs m0 m1 m2 HF E2 M01 -> a Ha Hn. rewrite <- (M01 a Ha Hn). apply HF. rewrite (wz a Ha).
  intros (r & Hin & Hr). cbv [fsT_ret_regions app In] in Hin.
  destruct Hin as [<-|[<-|[<-|[<-|[]]]]];
    cbv [fstk_ret fs_got_region fs_bcell_region decL_txr YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
    try rewrite E2 in Hr; unfold DEC_F in *; lia.
Qed.

Lemma decLO_meq_m : forall Ex d rs p (m0 m1 m2 : word -> option byte),
  bv_unsigned (ew Ex 2) = d_sp d - DEC_F -> bv_unsigned (ew Ex 47) = p -> frame_of Ex rs m1 m2 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (d_sp d - DEC_F <= a < d_sp d) -> a <> p ->
     m1 (Z_to_bv 64 a) = m0 (Z_to_bv 64 a)) ->
  rs = fsT_ret_regions DEC_F decL_cs [decL_str] ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (d_sp d - DEC_F <= a < d_sp d) -> a <> p ->
     m2 (Z_to_bv 64 a) = m0 (Z_to_bv 64 a)).
Proof.
  intros Ex d rs p m0 m1 m2 E2 E47 HF M01 -> a Ha Hn Hp. rewrite <- (M01 a Ha Hn Hp). apply HF. rewrite (wz a Ha).
  intros (r & Hin & Hr). cbv [fsT_ret_regions app In] in Hin.
  destruct Hin as [<-|[<-|[<-|[<-|[]]]]];
    cbv [fstk_ret fs_got_region fs_bcell_region decL_str YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
    try rewrite E2 in Hr; try rewrite E47 in Hr; unfold DEC_F in *; lia.
Qed.

(* one more atom fact on a state *)
Section A4. Context {fx : YK11.FPState}.
Lemma decLO_add_atom : forall E ss ms n f, st_ok tfibsegs E ss ms -> afact_ok E n f ->
  st_ok tfibsegs E (set_facts ss (mkFacts ((n, f) :: f_atoms (ss_facts ss)) (f_conds (ss_facts ss))
    (f_alias (ss_facts ss)))) ms.
Proof.
  intros E ss ms n f HS Hf. apply st_ok_set_facts; [exact HS|].
  apply facts_ok_add_atom; [exact (st_ok_facts_ok tfibsegs E ss ms HS) | exact Hf].
Qed.
End A4.

Section L4. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Hypothesis HSS : FsShadowSyms B.
(* the image facts (FSH_Rt.v:73-76), a Theorem Labs lane's decLB_g64 takes them *)
Hypothesis HIMG : fs_img_facts tfibsegs B.
(* the memchr interceptor's contract at fs.asan's PC_memchr (FSH_Gen.v:474, FSH_Rt.v FsRt.fr_memchr) *)
Hypothesis HMEMCHR : amemchr_realizesU tfibsegs B PC_memchr.

(* the byte of this arm: no NUL in the text (cstr), a byte (bytes_ok) *)
Lemma decLO_c : forall d i, dec_entry_ok B d -> (i < length (d_tb d))%nat -> 1 <= nth i (d_tb d) 0 <= 255.
Proof.
  intros d i HE Hi.
  pose proof HE as (_ & _ & _ & _ & _ & ((_ & HNZ) & _) & _ & HBO & _).
  assert (Hin : In (nth i (d_tb d) 0) (d_tb d)) by (apply nth_In; exact Hi).
  rewrite Forall_forall in HNZ. unfold WriterSpec.bytes_ok in HBO. rewrite Forall_forall in HBO.
  pose proof (HNZ _ Hin). pose proof (HBO _ Hin). lia.
Qed.

(* ==== the call of fuzz_free on a refused text, from the engine's state at A_fuzz_free ==== *)
Lemma decLO_free : forall d q i six pad acc Wc lyc Sc Uc regsc memc mdc k regs2 mem2 Ex ss ms md',
  dec_entry_ok B d -> dec_head B d q i six pad acc Wc lyc Sc Uc regsc memc mdc k ->
  (forall W3 ly3 S3 U3 regs3 mem3 md3 k3, dec_at_free B d q W3 ly3 S3 U3 regs3 mem3 md3 k3 ->
     SRr tfibsegs W3 (cfg_at tfibsegs A_fuzz_free regs3 mem3 md3) (dec_post B d)) ->
  decL_memf B d q six Wc lyc Sc mem2 ->
  (forall r, In r decLO_kregs -> getr regs2 r = getr regsc r) ->
  st_ok tfibsegs Ex ss (restrict (w_H Wc) ms) ->
  (forall n, (n < 48)%nat ->
     ew Ex n = ew (decL_E d regs2 [Z_to_bv 64 (q + Z.of_nat (length (WriterSpec.six_bytes six)))]) n) ->
  ss_pc ss = A_fuzz_free -> ss_resv ss = None -> ss_regs ss = decLO_fregs ->
  ss_mem ss = fsT_ret_regions DEC_F decL_cs [decL_str] ->
  dec_J B d lyc Sc Wc Uc (ms_mem ms) md' k -> ARU tfibsegs B lyc Sc Uc Wc (ms_mem ms) md' ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (d_sp d - DEC_F <= a < d_sp d) ->
     a <> q + Z.of_nat (length (WriterSpec.six_bytes six)) -> ms_mem ms (Z_to_bv 64 a) = mem2 (Z_to_bv 64 a)) ->
  WriterSpec.b64_dec (d_tb d) = None ->
  SRr tfibsegs Wc (mkCfg ms md') (dec_post B d).
Proof.
intros d q i six pad acc Wc lyc Sc Uc regsc memc mdc k regs2 mem2 Ex ss ms md' HE HH HFREE HM2 RK HS HEx Hpc Hrv
  Hregs Hmem HJ3 HARU3 MEQ Hdec.
pose proof HH as HH0. decL_unhead HH.
pose proof (fsw_sp B _ _ _ _ _ _ _ _ _ (proj1 (proj1 HE))) as (Hsp16 & Hspc & Hsp47 & _).
change (spZ (d_regs d)) with (d_sp d) in Hsp16, Hspc, Hsp47.
assert (FS : STK_preset_base64_decode = ltac:(let v := eval vm_compute in STK_preset_base64_decode in exact v)) by reflexivity.
pose proof (decL_lenp_range B d HE) as (L1 & L2 & _).
pose proof (decLB_q B d q i six pad acc Wc lyc Sc Uc regsc memc mdc k HE HH0) as (Q16 & Q1 & Q2 & Qn & _).
assert (Hnb : Z.of_nat (length (WriterSpec.six_bytes six)) < d_n d) by (unfold d_n; apply decLA_nbytes; lia).
assert (EK : forall (m : nat) (r : bv 5), (m < 48)%nat -> Z.of_nat m = bv_unsigned r -> In r decLO_kregs ->
  ew Ex m = getr regsc r)
  by (intros m r Hm Hr Hkin; rewrite (HEx m Hm), (decL_E_reg d regs2 _ m r Hr); exact (RK r Hkin)).
assert (GK : forall (r : bv 5) (m : nat), sr_get decLO_fregs r = SOff m 0 -> (m < 48)%nat -> Z.of_nat m = bv_unsigned r ->
  In r decLO_kregs -> getr (ms_regs ms) r = getr regsc r).
{ intros r m H1 Hm Hr Hkin. apply (decL_reg (w_H Wc) Ex ss ms r (SOff m 0)); [exact HS | rewrite Hregs; exact H1 |].
  rewrite fsw_SOff0. exact (EK m r Hm Hr Hkin). }
assert (E2 : bv_unsigned (ew Ex 2) = d_sp d - DEC_F) by (rewrite (EK 2%nat 2%bv ltac:(lia) eq_refl ltac:(decLO_in)); exact Hsp).
destruct (decL_frame_back d regs2 [Z_to_bv 64 (q + Z.of_nat (length (WriterSpec.six_bytes six)))] Wc ms Ex ss HS
  ltac:(rewrite Hmem; reflexivity) E2 (fun m Hm => HEx m ltac:(lia)) ltac:(lia)) as (HFr3 & HLs3).
apply (decL_free B d q i six pad acc Wc lyc Sc Uc regsc memc mdc k Ex ss ms md' HH0 HFREE HS Hrv Hpc HJ3 HARU3).
- apply (decLB_tr B d q i six pad acc Wc lyc Sc Uc regsc memc mdc k mem2 (ms_mem ms) HE HH0 HM2).
  intros a Ha H1 H2. apply aview_at. apply MEQ; [exact Ha | unfold DEC_F in *; lia | lia].
- exact HFr3.
- exact HLs3.
- apply (decL_reg (w_H Wc) Ex ss ms 10%bv (SOff 9 0)); [exact HS | rewrite Hregs; reflexivity |].
  rewrite fsw_SOff0, (EK 9%nat 9%bv ltac:(lia) eq_refl ltac:(decLO_in)). exact R9.
- exact (fsw_reg_lit (w_H Wc) Ex ss ms 1%bv 543100 HS ltac:(rewrite Hregs; reflexivity) ltac:(lia)).
- unfold spZ. rewrite (GK 2%bv 2%nat ltac:(vm_compute; reflexivity) ltac:(lia) eq_refl ltac:(decLO_in)). exact Hsp.
- rewrite (GK 3%bv 3%nat ltac:(vm_compute; reflexivity) ltac:(lia) eq_refl ltac:(decLO_in)). exact R3.
- rewrite (GK 4%bv 4%nat ltac:(vm_compute; reflexivity) ltac:(lia) eq_refl ltac:(decLO_in)). exact R4.
- rewrite (GK 8%bv 8%nat ltac:(vm_compute; reflexivity) ltac:(lia) eq_refl ltac:(decLO_in)). exact R8.
- exact Hdec.
Qed.

(* ==== the next head, bits = 0 (no byte stored) ==== *)
Lemma decLO_next0 : forall d q i six pad acc Wc lyc Sc Uc regsc memc mdc k regs2 mem2 v Ex ss ms md',
  dec_entry_ok B d -> dec_head B d q i six pad acc Wc lyc Sc Uc regsc memc mdc k ->
  (forall six' pad' acc' Wc' lyc' Sc' Uc' regsc' memc' mdc' k',
     dec_head B d q (S i) six' pad' acc' Wc' lyc' Sc' Uc' regsc' memc' mdc' k' ->
     SRr tfibsegs Wc' (mkCfg (YK11.mkst regsc' (Z_to_bv 64 DEC_HEAD) memc' (YK11.seg_rom tfibsegs)) mdc') (dec_post B d)) ->
  (i < length (d_tb d))%nat ->
  WriterSpec.b64_ws (nth i (d_tb d) 0) = false -> nth i (d_tb d) 0 <> 61 ->
  WriterSpec.b64v (nth i (d_tb d) 0) = Some v -> pad = 0 -> 6 * Z.of_nat (length six) mod 8 = 0 ->
  decL_memf B d q six Wc lyc Sc mem2 ->
  (forall r, In r decLO_kregs -> getr regs2 r = getr regsc r) -> getr regs2 10 = w64 (G_B64 + v) ->
  st_ok tfibsegs Ex ss (restrict (w_H Wc) ms) ->
  (forall n, (n < 48)%nat ->
     ew Ex n = ew (decL_E d regs2 [Z_to_bv 64 (q + Z.of_nat (length (WriterSpec.six_bytes six)))]) n) ->
  ss_pc ss = DEC_HEAD -> ss_resv ss = None -> ss_regs ss = decLO_hregs0 ->
  ss_mem ss = fsT_ret_regions DEC_F decL_cs [decL_str] ->
  dec_J B d lyc Sc Wc Uc (ms_mem ms) md' k -> ARU tfibsegs B lyc Sc Uc Wc (ms_mem ms) md' ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (d_sp d - DEC_F <= a < d_sp d) ->
     a <> q + Z.of_nat (length (WriterSpec.six_bytes six)) -> ms_mem ms (Z_to_bv 64 a) = mem2 (Z_to_bv 64 a)) ->
  SRr tfibsegs Wc (mkCfg ms md') (dec_post B d).
Proof.
intros d q i six pad acc Wc lyc Sc Uc regsc memc mdc k regs2 mem2 v Ex ss ms md' HE HH HIH Hilt Hws H61 Hv64 Hpad0 B0
  HM2 RK Rr HS HEx Hpc Hrv Hregs Hmem HJ3 HARU3 MEQ.
subst pad.
pose proof (decLA_skipn (d_tb d) i Hilt) as HSK.
pose proof HH as HH0. decL_unhead HH.
assert (HD : WriterSpec.b64_dec (d_tb d) = decLA_out 0 six (nth i (d_tb d) 0 :: skipn (S i) (d_tb d)))
  by (rewrite <- HSK; exact Hscan).
pose proof (decLA_b64v_range _ v Hv64) as Hv.
pose proof (fsw_sp B _ _ _ _ _ _ _ _ _ (proj1 (proj1 HE))) as (Hsp16 & Hspc & Hsp47 & _).
change (spZ (d_regs d)) with (d_sp d) in Hsp16, Hspc, Hsp47.
assert (FS : STK_preset_base64_decode = ltac:(let v := eval vm_compute in STK_preset_base64_decode in exact v)) by reflexivity.
pose proof (decL_lenp_range B d HE) as (L1 & L2 & _).
pose proof (decLB_q B d q i six 0 acc Wc lyc Sc Uc regsc memc mdc k HE HH0) as (Q16 & Q1 & Q2 & Qn & _).
pose proof HE as (_ & _ & _ & _ & _ & HCS & _ & _ & Htb & _).
pose proof HCS as (_ & Ht4096 & Htc & _).
assert (Hnb : Z.of_nat (length (WriterSpec.six_bytes six)) < d_n d) by (unfold d_n; apply decLA_nbytes; lia).
assert (EK : forall (m : nat) (r : bv 5), (m < 48)%nat -> Z.of_nat m = bv_unsigned r -> In r decLO_kregs ->
  ew Ex m = getr regsc r)
  by (intros m r Hm Hr Hkin; rewrite (HEx m Hm), (decL_E_reg d regs2 _ m r Hr); exact (RK r Hkin)).
assert (GR : forall (r : bv 5) e w, sr_get decLO_hregs0 r = e -> sv_denot Ex e = w -> getr (ms_regs ms) r = w)
  by (intros r e w H1 H2; apply (decL_reg (w_H Wc) Ex ss ms r e w HS); [rewrite Hregs; exact H1 | exact H2]).
assert (GK : forall (r : bv 5) (m : nat), sr_get decLO_hregs0 r = SOff m 0 -> (m < 48)%nat -> Z.of_nat m = bv_unsigned r ->
  In r decLO_kregs -> getr (ms_regs ms) r = getr regsc r)
  by (intros r m H1 Hm Hr Hkin; apply (GR r (SOff m 0)); [exact H1 | rewrite fsw_SOff0; exact (EK m r Hm Hr Hkin)]).
assert (E2 : bv_unsigned (ew Ex 2) = d_sp d - DEC_F) by (rewrite (EK 2%nat 2%bv ltac:(lia) eq_refl ltac:(decLO_in)); exact Hsp).
assert (E10 : ew Ex 10 = Z_to_bv 64 (G_B64 + v))
  by (rewrite (HEx 10%nat ltac:(lia)), (decL_E_reg d regs2 _ 10 10%bv eq_refl); exact Rr).
assert (E18 : ew Ex 18 = w64 (d_text d + Z.of_nat i)) by (rewrite (EK 18%nat 18%bv ltac:(lia) eq_refl ltac:(decLO_in)); exact R18).
assert (E19 : ew Ex 19 = Z_to_bv 64 G_B64) by (rewrite (EK 19%nat 19%bv ltac:(lia) eq_refl ltac:(decLO_in)); exact R19).
assert (E20 : ew Ex 20 = w64 (d_text d + Z.of_nat i)) by (rewrite (EK 20%nat 20%bv ltac:(lia) eq_refl ltac:(decLO_in)); exact R20).
assert (E23 : ew Ex 23 = Z_to_bv 64 acc) by (rewrite (EK 23%nat 23%bv ltac:(lia) eq_refl ltac:(decLO_in)); exact R23).
assert (E24 : ew Ex 24 = w64 0)
  by (rewrite (EK 24%nat 24%bv ltac:(lia) eq_refl ltac:(decLO_in)), R24, B0; reflexivity).
pose proof (decLO_acc Ex acc v E10 Hv E19 E23 Hacc) as HA.
destruct (decL_frame_back d regs2 [Z_to_bv 64 (q + Z.of_nat (length (WriterSpec.six_bytes six)))] Wc ms Ex ss HS
  ltac:(rewrite Hmem; reflexivity) E2 (fun m Hm => HEx m ltac:(lia)) ltac:(lia)) as (HFr3 & HLs3).
assert (HM3 : decL_memf B d q six Wc lyc Sc (ms_mem ms)).
{ apply (decLB_tr B d q i six 0 acc Wc lyc Sc Uc regsc memc mdc k mem2 (ms_mem ms) HE HH0 HM2).
  intros a Ha H1 H2. apply aview_at. apply MEQ; [exact Ha | unfold DEC_F in *; lia | lia]. }
assert (Hsn : WriterSpec.six_bytes (six ++ [v]) = WriterSpec.six_bytes six) by (apply decLA_snoc0; exact B0).
rewrite (st_ok_restrict_mkst tfibsegs (w_H Wc) Ex ss ms HS Hrv), Hpc.
apply (HIH (six ++ [v]) 0 (U Ex decLO_acc_e) Wc lyc Sc Uc (ms_regs ms) (ms_mem ms) md' k).
apply (decL_mk_head B d q i six 0 acc Wc lyc Sc Uc regsc memc mdc k (S i) (six ++ [v]) 0 (U Ex decLO_acc_e)
  (ms_regs ms) (ms_mem ms) md' HH0 HJ3 HARU3).
- unfold decL_memf in HM3 |- *. rewrite Hsn. exact HM3.
- exact HFr3.
- exact HLs3.
- unfold spZ. rewrite (GK 2%bv 2%nat ltac:(vm_compute; reflexivity) ltac:(lia) eq_refl ltac:(decLO_in)). exact Hsp.
- rewrite (GK 3%bv 3%nat ltac:(vm_compute; reflexivity) ltac:(lia) eq_refl ltac:(decLO_in)). exact R3.
- rewrite (GK 4%bv 4%nat ltac:(vm_compute; reflexivity) ltac:(lia) eq_refl ltac:(decLO_in)). exact R4.
- rewrite (GK 8%bv 8%nat ltac:(vm_compute; reflexivity) ltac:(lia) eq_refl ltac:(decLO_in)). exact R8.
- rewrite (GK 9%bv 9%nat ltac:(vm_compute; reflexivity) ltac:(lia) eq_refl ltac:(decLO_in)). exact R9.
- apply (GR 18%bv (SOff 18 1)); [vm_compute; reflexivity|].
  rewrite (decL_soff Ex 18 1 (d_text d + Z.of_nat i) E18) by lia. f_equal. lia.
- rewrite (GK 19%bv 19%nat ltac:(vm_compute; reflexivity) ltac:(lia) eq_refl ltac:(decLO_in)). exact R19.
- apply (GR 20%bv (SOff 20 1)); [vm_compute; reflexivity|].
  rewrite (decL_soff Ex 20 1 (d_text d + Z.of_nat i) E20) by lia. f_equal. lia.
- rewrite (GK 21%bv 21%nat ltac:(vm_compute; reflexivity) ltac:(lia) eq_refl ltac:(decLO_in)). exact R21.
- rewrite Hsn. rewrite (GK 22%bv 22%nat ltac:(vm_compute; reflexivity) ltac:(lia) eq_refl ltac:(decLO_in)). exact R22.
- apply (GR 23%bv decLO_acc_e); [vm_compute; reflexivity|]. unfold w64. apply denot_lit_U.
- pose proof (U_range Ex decLO_acc_e) as X. unfold M64 in X. exact X.
- apply (GR 24%bv (SOff 24 6)); [vm_compute; reflexivity|].
  rewrite (decL_soff Ex 24 6 0 E24) by lia. f_equal.
  rewrite length_app. cbn [length]. rewrite Nat2Z.inj_add. change (Z.of_nat 1) with 1.
  rewrite decLA_bits by lia. rewrite B0. reflexivity.
- rewrite (GK 25%bv 25%nat ltac:(vm_compute; reflexivity) ltac:(lia) eq_refl ltac:(decLO_in)). exact R25.
- exact (fsw_reg_lit (w_H Wc) Ex ss ms 26%bv 0 HS ltac:(rewrite Hregs; reflexivity) ltac:(lia)).
- rewrite (GK 27%bv 27%nat ltac:(vm_compute; reflexivity) ltac:(lia) eq_refl ltac:(decLO_in)). exact R27.
- lia.
- lia.
- rewrite length_app. cbn [length]. lia.
- apply Forall_app. split; [exact Hsix64 | constructor; [lia | constructor]].
- rewrite last_last.
  replace (U Ex decLO_acc_e mod 64) with ((U Ex decLO_acc_e mod 4096) mod 64) by (Z.div_mod_to_equations; lia).
  rewrite HA. pose proof (Z.mod_pos_bound acc 64 ltac:(lia)). Z.div_mod_to_equations; lia.
- change (WriterSpec.b64_dec (d_tb d) = decLA_out 0 (six ++ [v]) (skipn (S i) (d_tb d))).
  rewrite HD. apply decLA_out_val; assumption.
Qed.

(* ==== the next head, bits in [2, 6] (one byte stored at q + n) ==== *)
Lemma decLO_next2 : forall d q i six pad acc Wc lyc Sc Uc regsc memc mdc k regs2 mem2 v Ex ss ms md',
  dec_entry_ok B d -> dec_head B d q i six pad acc Wc lyc Sc Uc regsc memc mdc k ->
  (forall six' pad' acc' Wc' lyc' Sc' Uc' regsc' memc' mdc' k',
     dec_head B d q (S i) six' pad' acc' Wc' lyc' Sc' Uc' regsc' memc' mdc' k' ->
     SRr tfibsegs Wc' (mkCfg (YK11.mkst regsc' (Z_to_bv 64 DEC_HEAD) memc' (YK11.seg_rom tfibsegs)) mdc') (dec_post B d)) ->
  (i < length (d_tb d))%nat ->
  WriterSpec.b64_ws (nth i (d_tb d) 0) = false -> nth i (d_tb d) 0 <> 61 ->
  WriterSpec.b64v (nth i (d_tb d) 0) = Some v -> pad = 0 -> 2 <= 6 * Z.of_nat (length six) mod 8 ->
  decL_memf B d q six Wc lyc Sc mem2 ->
  (forall r, In r decLO_kregs -> getr regs2 r = getr regsc r) -> getr regs2 10 = w64 (G_B64 + v) ->
  st_ok tfibsegs Ex ss (restrict (w_H Wc) ms) ->
  (forall n, (n < 48)%nat ->
     ew Ex n = ew (decL_E d regs2 [Z_to_bv 64 (q + Z.of_nat (length (WriterSpec.six_bytes six)))]) n) ->
  ss_pc ss = DEC_HEAD -> ss_resv ss = None -> ss_regs ss = decLO_hregs2 ->
  ss_mem ss = fsT_ret_regions DEC_F decL_cs [decLO_str2] ->
  dec_J B d lyc Sc Wc Uc (ms_mem ms) md' k -> ARU tfibsegs B lyc Sc Uc Wc (ms_mem ms) md' ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (d_sp d - DEC_F <= a < d_sp d) ->
     a <> q + Z.of_nat (length (WriterSpec.six_bytes six)) -> ms_mem ms (Z_to_bv 64 a) = mem2 (Z_to_bv 64 a)) ->
  SRr tfibsegs Wc (mkCfg ms md') (dec_post B d).
Proof.
intros d q i six pad acc Wc lyc Sc Uc regsc memc mdc k regs2 mem2 v Ex ss ms md' HE HH HIH Hilt Hws H61 Hv64 Hpad0 B26
  HM2 RK Rr HS HEx Hpc Hrv Hregs Hmem HJ3 HARU3 MEQ.
subst pad.
pose proof (decLA_skipn (d_tb d) i Hilt) as HSK.
pose proof HH as HH0. decL_unhead HH.
assert (HD : WriterSpec.b64_dec (d_tb d) = decLA_out 0 six (nth i (d_tb d) 0 :: skipn (S i) (d_tb d)))
  by (rewrite <- HSK; exact Hscan).
pose proof (decLA_b64v_range _ v Hv64) as Hv.
pose proof (fsw_sp B _ _ _ _ _ _ _ _ _ (proj1 (proj1 HE))) as (Hsp16 & Hspc & Hsp47 & _).
change (spZ (d_regs d)) with (d_sp d) in Hsp16, Hspc, Hsp47.
assert (FS : STK_preset_base64_decode = ltac:(let v := eval vm_compute in STK_preset_base64_decode in exact v)) by reflexivity.
pose proof asan_consts as (Cc1 & _).
pose proof (decL_lenp_range B d HE) as (L1 & L2 & _).
pose proof (decLB_q B d q i six 0 acc Wc lyc Sc Uc regsc memc mdc k HE HH0) as (Q16 & Q1 & Q2 & Qn & _).
assert (Hq4096 : 4096 <= q) by (unfold HEAD in Q1; lia).
pose proof HE as (_ & _ & _ & _ & _ & HCS & _ & _ & Htb & _).
pose proof HCS as (_ & Ht4096 & Htc & _).
assert (Hnb : Z.of_nat (length (WriterSpec.six_bytes six)) < d_n d) by (unfold d_n; apply decLA_nbytes; lia).
assert (Hbits : 6 * Z.of_nat (length six) mod 8 <= 6) by (pose proof (Z.mod_pos_bound (6 * Z.of_nat (length six)) 8); lia).
assert (EK : forall (m : nat) (r : bv 5), (m < 48)%nat -> Z.of_nat m = bv_unsigned r -> In r decLO_kregs ->
  ew Ex m = getr regsc r)
  by (intros m r Hm Hr Hkin; rewrite (HEx m Hm), (decL_E_reg d regs2 _ m r Hr); exact (RK r Hkin)).
assert (GR : forall (r : bv 5) e w, sr_get decLO_hregs2 r = e -> sv_denot Ex e = w -> getr (ms_regs ms) r = w)
  by (intros r e w H1 H2; apply (decL_reg (w_H Wc) Ex ss ms r e w HS); [rewrite Hregs; exact H1 | exact H2]).
assert (GK : forall (r : bv 5) (m : nat), sr_get decLO_hregs2 r = SOff m 0 -> (m < 48)%nat -> Z.of_nat m = bv_unsigned r ->
  In r decLO_kregs -> getr (ms_regs ms) r = getr regsc r)
  by (intros r m H1 Hm Hr Hkin; apply (GR r (SOff m 0)); [exact H1 | rewrite fsw_SOff0; exact (EK m r Hm Hr Hkin)]).
assert (E2 : bv_unsigned (ew Ex 2) = d_sp d - DEC_F) by (rewrite (EK 2%nat 2%bv ltac:(lia) eq_refl ltac:(decLO_in)); exact Hsp).
assert (E10 : ew Ex 10 = Z_to_bv 64 (G_B64 + v))
  by (rewrite (HEx 10%nat ltac:(lia)), (decL_E_reg d regs2 _ 10 10%bv eq_refl); exact Rr).
assert (E18 : ew Ex 18 = w64 (d_text d + Z.of_nat i)) by (rewrite (EK 18%nat 18%bv ltac:(lia) eq_refl ltac:(decLO_in)); exact R18).
assert (E19 : ew Ex 19 = Z_to_bv 64 G_B64) by (rewrite (EK 19%nat 19%bv ltac:(lia) eq_refl ltac:(decLO_in)); exact R19).
assert (E20 : ew Ex 20 = w64 (d_text d + Z.of_nat i)) by (rewrite (EK 20%nat 20%bv ltac:(lia) eq_refl ltac:(decLO_in)); exact R20).
assert (E22 : ew Ex 22 = w64 (Z.of_nat (length (WriterSpec.six_bytes six))))
  by (rewrite (EK 22%nat 22%bv ltac:(lia) eq_refl ltac:(decLO_in)); exact R22).
assert (E23 : ew Ex 23 = Z_to_bv 64 acc) by (rewrite (EK 23%nat 23%bv ltac:(lia) eq_refl ltac:(decLO_in)); exact R23).
assert (E24 : ew Ex 24 = w64 (6 * Z.of_nat (length six) mod 8))
  by (rewrite (EK 24%nat 24%bv ltac:(lia) eq_refl ltac:(decLO_in)); exact R24).
assert (E47 : ew Ex 47 = Z_to_bv 64 (q + Z.of_nat (length (WriterSpec.six_bytes six))))
  by (rewrite (HEx 47%nat ltac:(lia)); exact (decL_E_ex d regs2 _ 0)).
assert (E47u : bv_unsigned (ew Ex 47) = q + Z.of_nat (length (WriterSpec.six_bytes six)))
  by (rewrite E47; apply wz; lia).
pose proof (decLO_acc Ex acc v E10 Hv E19 E23 Hacc) as HA.
destruct (decL_frame_back d regs2 [Z_to_bv 64 (q + Z.of_nat (length (WriterSpec.six_bytes six)))] Wc ms Ex ss HS
  ltac:(rewrite Hmem; reflexivity) E2 (fun m Hm => HEx m ltac:(lia)) ltac:(lia)) as (HFr3 & HLs3).
(* the stored byte, read back from the store region *)
set (b := Z.shiftr (last six 0 * 64 + v) (6 * Z.of_nat (length six) mod 8 - 2) mod 256).
assert (Hsnoc : WriterSpec.six_bytes (six ++ [v]) = WriterSpec.six_bytes six ++ [b])
  by (unfold b; apply decLA_snoc; [exact Hsix64 | exact Hv | exact B26]).
assert (HAV : aview tfibsegs (w_H Wc) (ms_mem ms) (q + Z.of_nat (length (WriterSpec.six_bytes six))) = Some b).
{ pose proof (fsw_region_nth Ex ss (restrict (w_H Wc) ms) 3 decLO_str2 HS ltac:(rewrite Hmem; reflexivity)) as HR.
  cbn [ms_mem restrict] in HR.
  rewrite <- E47u. rewrite (decLO_str2_aview Ex (w_H Wc) (ms_mem ms) HR). f_equal.
  rewrite (decLA_byte Ex decLO_acc_e (6 * Z.of_nat (length six) mod 8) E24) by lia.
  rewrite HA, Hlast. reflexivity. }
assert (HM3 : decL_memf B d q (six ++ [v]) Wc lyc Sc (ms_mem ms)).
{ apply (decLB_store B d q i six 0 acc Wc lyc Sc Uc regsc memc mdc k mem2 (ms_mem ms) (d_sp d - DEC_F) (d_sp d)
    (six ++ [v]) b HE HH0 HM2 ltac:(unfold DEC_F; lia) ltac:(lia) Hnb).
  - intros a Ha H1 H2. apply aview_at. exact (MEQ a Ha H1 H2).
  - exact HAV.
  - unfold b. apply Z.mod_pos_bound. lia.
  - exact Hsnoc. }
rewrite (st_ok_restrict_mkst tfibsegs (w_H Wc) Ex ss ms HS Hrv), Hpc.
apply (HIH (six ++ [v]) 0 (U Ex decLO_acc_e) Wc lyc Sc Uc (ms_regs ms) (ms_mem ms) md' k).
apply (decL_mk_head B d q i six 0 acc Wc lyc Sc Uc regsc memc mdc k (S i) (six ++ [v]) 0 (U Ex decLO_acc_e)
  (ms_regs ms) (ms_mem ms) md' HH0 HJ3 HARU3 HM3 HFr3 HLs3).
- unfold spZ. rewrite (GK 2%bv 2%nat ltac:(vm_compute; reflexivity) ltac:(lia) eq_refl ltac:(decLO_in)). exact Hsp.
- rewrite (GK 3%bv 3%nat ltac:(vm_compute; reflexivity) ltac:(lia) eq_refl ltac:(decLO_in)). exact R3.
- rewrite (GK 4%bv 4%nat ltac:(vm_compute; reflexivity) ltac:(lia) eq_refl ltac:(decLO_in)). exact R4.
- rewrite (GK 8%bv 8%nat ltac:(vm_compute; reflexivity) ltac:(lia) eq_refl ltac:(decLO_in)). exact R8.
- rewrite (GK 9%bv 9%nat ltac:(vm_compute; reflexivity) ltac:(lia) eq_refl ltac:(decLO_in)). exact R9.
- apply (GR 18%bv (SOff 18 1)); [vm_compute; reflexivity|].
  rewrite (decL_soff Ex 18 1 (d_text d + Z.of_nat i) E18) by lia. f_equal. lia.
- rewrite (GK 19%bv 19%nat ltac:(vm_compute; reflexivity) ltac:(lia) eq_refl ltac:(decLO_in)). exact R19.
- apply (GR 20%bv (SOff 20 1)); [vm_compute; reflexivity|].
  rewrite (decL_soff Ex 20 1 (d_text d + Z.of_nat i) E20) by lia. f_equal. lia.
- rewrite (GK 21%bv 21%nat ltac:(vm_compute; reflexivity) ltac:(lia) eq_refl ltac:(decLO_in)). exact R21.
- apply (GR 22%bv (SOff 22 1)); [vm_compute; reflexivity|].
  rewrite (decL_soff Ex 22 1 (Z.of_nat (length (WriterSpec.six_bytes six))) E22) by lia. f_equal.
  rewrite Hsnoc, length_app. cbn [length]. lia.
- apply (GR 23%bv decLO_acc_e); [vm_compute; reflexivity|]. unfold w64. apply denot_lit_U.
- pose proof (U_range Ex decLO_acc_e) as X. unfold M64 in X. exact X.
- apply (GR 24%bv (SOff 24 (-2))); [vm_compute; reflexivity|].
  rewrite (decL_soff Ex 24 (-2) (6 * Z.of_nat (length six) mod 8) E24) by lia. f_equal.
  rewrite length_app. cbn [length]. rewrite Nat2Z.inj_add. change (Z.of_nat 1) with 1.
  rewrite decLA_bits by lia. destruct (Z.eqb_spec (6 * Z.of_nat (length six) mod 8) 0); lia.
- rewrite (GK 25%bv 25%nat ltac:(vm_compute; reflexivity) ltac:(lia) eq_refl ltac:(decLO_in)). exact R25.
- exact (fsw_reg_lit (w_H Wc) Ex ss ms 26%bv 0 HS ltac:(rewrite Hregs; reflexivity) ltac:(lia)).
- rewrite (GK 27%bv 27%nat ltac:(vm_compute; reflexivity) ltac:(lia) eq_refl ltac:(decLO_in)). exact R27.
- lia.
- lia.
- rewrite length_app. cbn [length]. lia.
- apply Forall_app. split; [exact Hsix64 | constructor; [lia | constructor]].
- rewrite last_last.
  replace (U Ex decLO_acc_e mod 64) with ((U Ex decLO_acc_e mod 4096) mod 64) by (Z.div_mod_to_equations; lia).
  rewrite HA. pose proof (Z.mod_pos_bound acc 64 ltac:(lia)). Z.div_mod_to_equations; lia.
- change (WriterSpec.b64_dec (d_tb d) = decLA_out 0 (six ++ [v]) (skipn (S i) (d_tb d))).
  rewrite HD. apply decLA_out_val; assumption.
Qed.

(* ==== after memchr returned r (pc 0x848fc): the canonical state decL_mss, then `beqz r`, `bnez s10`, the sextet ====
   Cut into lemmas (the one-proof draft ran past 900 s): the facts the cases read (decLO_mfacts), the state decL_mss
   and its shadow entry (decLO_mss_ok, decLO_msh_ok, over the pure decLO_mgf_ok / decLO_str_ok / decLO_mpd), the
   r = 0 arm (decLT_none), the r <> 0 arm (decLT_some: pad <> 0 to fuzz_free, else bits = 0 / bits in [2, 6] to the
   next head), and decLO_tail, which only branches on r. *)
(* a register this arm keeps, read in the env of the cut after memchr *)
Lemma decLO_ek : forall d regs2 regsc ex (m : nat) (r : bv 5), Z.of_nat m = bv_unsigned r -> In r decLO_kregs ->
  (forall r, In r decLO_kregs -> getr regs2 r = getr regsc r) -> ew (decL_E d regs2 ex) m = getr regsc r.
Proof. intros d regs2 regsc ex m r Hm Hr RK. rewrite (decL_E_reg d regs2 ex m r Hm). exact (RK r Hr). Qed.

(* the bits count 6 * |six| mod 8 is even and at most 6 *)
Lemma decLO_bits : forall L, 0 <= L -> 0 <= 6 * L mod 8 <= 6 /\ (6 * L mod 8) mod 2 = 0.
Proof. intros L HL. destruct (decLA_bits_cases L HL) as [E|[E|[E|E]]]; rewrite E; split; first [lia | reflexivity]. Qed.

(* the block's size bound: at most 2^28 text bytes *)
Lemma decLO_dn : forall d, dec_entry_ok B d -> d_n d <= 2 ^ 28.
Proof.
  intros d HE. pose proof HE as (_ & _ & _ & _ & _ & _ & _ & _ & HLEN & _).
  unfold d_n, dec_size.
  assert (A : Z.of_nat (length (d_tb d)) / 4 <= 2 ^ 28 / 4) by (apply Z.div_le_mono; lia).
  change (2 ^ 28 / 4) with 67108864 in A. lia.
Qed.

(* the head facts this arm reads *)
Lemma decLO_hd : forall d q i six pad acc Wc lyc Sc Uc regsc memc mdc k,
  dec_head B d q i six pad acc Wc lyc Sc Uc regsc memc mdc k ->
  spZ regsc = d_sp d - DEC_F /\ (length six <= i)%nat /\ 0 <= pad <= Z.of_nat i /\
  getr regsc 24 = w64 (6 * Z.of_nat (length six) mod 8) /\ getr regsc 26 = w64 pad /\ getr regsc 21 = w64 SHADOW_OFF /\
  WriterSpec.b64_dec (d_tb d) = decLA_out pad six (skipn i (d_tb d)).
Proof.
intros d q i six pad acc Wc lyc Sc Uc regsc memc mdc k HH. decL_unhead HH.
exact (conj Hsp (conj Hsix (conj Hpad (conj R24 (conj R26 (conj R21 Hscan)))))).
Qed.

Lemma decLO_mfacts : forall d q i six pad acc Wc lyc Sc Uc regsc memc mdc k regs2,
  dec_entry_ok B d -> dec_head B d q i six pad acc Wc lyc Sc Uc regsc memc mdc k ->
  (i < length (d_tb d))%nat -> (forall r, In r decLO_kregs -> getr regs2 r = getr regsc r) ->
  bv_unsigned (ew (decL_E d regs2 [Z_to_bv 64 (q + Z.of_nat (length (WriterSpec.six_bytes six)))]) 2) = d_sp d - DEC_F /\
  bv_unsigned (ew (decL_E d regs2 [Z_to_bv 64 (q + Z.of_nat (length (WriterSpec.six_bytes six)))]) 47) =
    q + Z.of_nat (length (WriterSpec.six_bytes six)) /\
  d_sp d <= d_ot d /\
  in_tmp_block (ablocks B (d_ly d) (d_S d)) (ablocks B lyc Sc) (q + Z.of_nat (length (WriterSpec.six_bytes six))) /\
  Z.of_nat (length (WriterSpec.six_bytes six)) < d_n d /\
  WriterSpec.b64_dec (d_tb d) = decLA_out pad six (nth i (d_tb d) 0 :: skipn (S i) (d_tb d)).
Proof.
intros d q i six pad acc Wc lyc Sc Uc regsc memc mdc k regs2 HE HH Hilt RK.
pose proof asan_consts as ((C1 & C2) & _).
pose proof (decLB_q B d q i six pad acc Wc lyc Sc Uc regsc memc mdc k HE HH) as (_ & Q1 & Q2 & _ & _ & _ & Qa).
unfold HEAD in Q1.
pose proof (decLB_sp B d HE) as (_ & SP2 & _).
destruct (decLO_hd d q i six pad acc Wc lyc Sc Uc regsc memc mdc k HH) as (Hsp & Hsix & _ & _ & _ & _ & Hscan).
assert (Hnb : Z.of_nat (length (WriterSpec.six_bytes six)) < d_n d)
  by (unfold d_n; apply decLA_nbytes; lia).
assert (E47 : ew (decL_E d regs2 [Z_to_bv 64 (q + Z.of_nat (length (WriterSpec.six_bytes six)))]) 47 =
  Z_to_bv 64 (q + Z.of_nat (length (WriterSpec.six_bytes six)))) by exact (decL_E_ex d regs2 _ 0).
destruct (Qa (q + Z.of_nat (length (WriterSpec.six_bytes six))) ltac:(lia)) as (_ & Htmp & _ & _).
split; [rewrite (decLO_ek d regs2 regsc [Z_to_bv 64 (q + Z.of_nat (length (WriterSpec.six_bytes six)))] 2 2%bv eq_refl
  ltac:(decLO_in) RK); exact Hsp|].
split; [rewrite E47; apply wz; lia|].
split; [exact SP2|]. split; [exact Htmp|]. split; [exact Hnb|].
rewrite <- (decLA_skipn (d_tb d) i Hilt). exact Hscan.
Qed.

(* the atom facts of decL_mgf from the values of the kept registers and of atom 47 = q + n *)
Lemma decLO_mgf_ok : forall (E : env) q n tx acc bits pad,
  ew E 8 = w64 DEC_WSMASK -> ew E 9 = w64 q -> ew E 18 = w64 tx -> ew E 19 = w64 G_B64 -> ew E 20 = w64 tx ->
  ew E 21 = w64 SHADOW_OFF -> ew E 22 = w64 n -> ew E 23 = w64 acc -> ew E 24 = w64 bits -> ew E 25 = w64 61 ->
  ew E 26 = w64 pad -> ew E 27 = w64 2 -> bv_unsigned (ew E 47) = q + n ->
  4096 + HEAD <= q -> q mod 16 = 0 -> 0 <= n <= 2 ^ 30 -> q + n < DEC_CEIL ->
  4096 <= tx <= DEC_CEIL -> 0 <= acc < 2 ^ 64 -> 0 <= bits <= 6 -> bits mod 2 = 0 -> 0 <= pad <= 2 ^ 28 ->
  atoms_ok E decL_mgf.
Proof.
intros E q n tx acc bits pad E8 E9 E18 E19 E20 E21 E22 E23 E24 E25 E26 E27 E47 Hq Hq16 Hn Hqn Htx Hacc Hb Hb2 Hp.
unfold DEC_CEIL, HEAD in *.
unfold decL_mgf, decL_sgf. cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E47, E8, E9, E18, E19, E20, E21, E22, E23, E24, E25, E26, E27.
rewrite (decL_w64u DEC_WSMASK) by (unfold DEC_WSMASK; lia).
rewrite (decL_w64u q), (decL_w64u tx), (decL_w64u n), (decL_w64u acc), (decL_w64u bits), (decL_w64u pad) by lia.
rewrite (decL_w64u G_B64) by (unfold G_B64; lia).
rewrite (decL_w64u SHADOW_OFF) by (unfold SHADOW_OFF; lia).
rewrite (decL_w64u 61), (decL_w64u 2) by lia.
change (2 ^ 0) with 1. change (2 ^ 4) with 16. change (2 ^ 1) with 2. rewrite !Z.mod_1_r.
unfold DEC_WSMASK, G_B64, SHADOW_OFF, DEC_CEIL, HEAD.
repeat match goal with |- _ /\ _ => split end; try exact I; lia.
Qed.

(* the store region decL_str (one writable byte at atom 47) *)
Lemma decLO_str_ok : forall (E : env) (H : word -> bool) (m : word -> option byte) p,
  bv_unsigned (ew E 47) = p -> 0 <= p -> p + 1 <= 2 ^ 64 -> writable_at tfibsegs (mrestrict H m) p ->
  Forall (region_ok tfibsegs E (mrestrict H m)) [decL_str].
Proof.
intros E H m p E47 H0 H1 Hw. constructor; [|constructor].
unfold decL_str, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite E47. split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. replace (p + o) with p by lia. exact Hw.
Qed.

(* the regions of decL_mss are apart: the frame at b = sp - 112, the two shadow-base cells, the store byte p *)
Lemma decLO_mpd : forall (E : env) b p,
  bv_unsigned (ew E 2) = b -> bv_unsigned (ew E 47) = p -> p + 1 <= b -> alloc_ceiling <= b ->
  (p + 1 <= tfib_D_GOT_asan_shadow_memory_dynamic_address \/ tfib_D_GOT_asan_shadow_memory_dynamic_address + 8 <= p) ->
  (p + 1 <= tfib_D_asan_shadow_memory_dynamic_address \/ tfib_D_asan_shadow_memory_dynamic_address + 8 <= p) ->
  pairwise_disjoint E (fsT_ret_regions DEC_F decL_cs [decL_str]).
Proof.
intros E b p E2 E47 Hpb Hb G1 G2. pose proof asan_consts as ((C1 & _) & _).
apply pairwise_disjoint_of_extents.
unfold fsT_ret_regions, fstk_ret, fs_got_region, fs_bcell_region, decL_str, extent_of_region.
cbn [map app YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E2, E47.
unfold tfib_D_GOT_asan_shadow_memory_dynamic_address, tfib_D_asan_shadow_memory_dynamic_address, DEC_F in *.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
repeat match goal with |- _ /\ _ => split end; try exact I; lia.
Qed.

(* the state at the return of memchr: decL_mss over the env decL_E d regs2 [q + n] *)
Lemma decLO_mss_ok : forall d q i six pad acc Wc lyc Sc Uc regsc memc mdc k regs2 mem2 md2,
  dec_entry_ok B d -> dec_head B d q i six pad acc Wc lyc Sc Uc regsc memc mdc k ->
  (i < length (d_tb d))%nat ->
  dec_J B d lyc Sc Wc Uc mem2 md2 k -> ARU tfibsegs B lyc Sc Uc Wc mem2 md2 ->
  dec_frame_ok Wc mem2 (d_sp d - DEC_F) (d_regs d) -> dec_lenp_slot Wc mem2 (d_sp d - DEC_F) (d_lenp d) ->
  (forall r, In r decLO_kregs -> getr regs2 r = getr regsc r) ->
  st_ok tfibsegs (decL_E d regs2 [Z_to_bv 64 (q + Z.of_nat (length (WriterSpec.six_bytes six)))]) decL_mss
    (restrict (w_H Wc) (YK11.mkst regs2 (Z_to_bv 64 DEC_RA_MEMCHR) mem2 (YK11.seg_rom tfibsegs))).
Proof.
intros d q i six pad acc Wc lyc Sc Uc regsc memc mdc k regs2 mem2 md2 HE HH Hilt HJ2 HARU2 HFr2 HLs2 RK.
pose proof asan_consts as ((C1 & C2) & _).
destruct (decLO_mfacts d q i six pad acc Wc lyc Sc Uc regsc memc mdc k regs2 HE HH Hilt RK)
  as (E2 & E47u & _ & _ & Hnb & _).
pose proof (decLB_q B d q i six pad acc Wc lyc Sc Uc regsc memc mdc k HE HH) as (Q16 & Q1 & Q2 & _ & _ & _ & Qa).
pose proof (decLB_text B d q i six pad acc Wc lyc Sc Uc regsc memc mdc k HE HH) as (T1 & T2 & _).
pose proof (decLB_sp B d HE) as (SP1 & _ & _).
pose proof (decLB_qw B d q i six pad acc Wc lyc Sc Uc regsc memc mdc k mem2 md2 HE HH HARU2) as HQW.
pose proof (decLO_dn d HE) as Hdn.
pose proof (WriterSpecFacts.six_bytes_length six) as Hnbl.
pose proof HE as (_ & _ & _ & _ & _ & _ & _ & _ & HLEN & _).
pose proof (decLO_bits (Z.of_nat (length six)) ltac:(lia)) as (Hb1 & Hb2).
destruct (Qa (q + Z.of_nat (length (WriterSpec.six_bytes six))) ltac:(lia)) as (_ & _ & G1 & G2).
clear Qa.
pose proof HH as HH0. decL_unhead HH0.
set (n := Z.of_nat (length (WriterSpec.six_bytes six))) in *.
set (Em := decL_E d regs2 [Z_to_bv 64 (q + n)]) in *.
assert (E8 : ew Em 8 = w64 DEC_WSMASK) by exact (eq_trans (decLO_ek d regs2 regsc _ 8 8%bv eq_refl ltac:(decLO_in) RK) R8).
assert (E9 : ew Em 9 = w64 q) by exact (eq_trans (decLO_ek d regs2 regsc _ 9 9%bv eq_refl ltac:(decLO_in) RK) R9).
assert (E18 : ew Em 18 = w64 (d_text d + Z.of_nat i))
  by exact (eq_trans (decLO_ek d regs2 regsc _ 18 18%bv eq_refl ltac:(decLO_in) RK) R18).
assert (E19 : ew Em 19 = w64 G_B64) by exact (eq_trans (decLO_ek d regs2 regsc _ 19 19%bv eq_refl ltac:(decLO_in) RK) R19).
assert (E20 : ew Em 20 = w64 (d_text d + Z.of_nat i))
  by exact (eq_trans (decLO_ek d regs2 regsc _ 20 20%bv eq_refl ltac:(decLO_in) RK) R20).
assert (E21 : ew Em 21 = w64 SHADOW_OFF)
  by exact (eq_trans (decLO_ek d regs2 regsc _ 21 21%bv eq_refl ltac:(decLO_in) RK) R21).
assert (E22 : ew Em 22 = w64 n) by exact (eq_trans (decLO_ek d regs2 regsc _ 22 22%bv eq_refl ltac:(decLO_in) RK) R22).
assert (E23 : ew Em 23 = w64 acc) by exact (eq_trans (decLO_ek d regs2 regsc _ 23 23%bv eq_refl ltac:(decLO_in) RK) R23).
assert (E24 : ew Em 24 = w64 (6 * Z.of_nat (length six) mod 8))
  by exact (eq_trans (decLO_ek d regs2 regsc _ 24 24%bv eq_refl ltac:(decLO_in) RK) R24).
assert (E25 : ew Em 25 = w64 61) by exact (eq_trans (decLO_ek d regs2 regsc _ 25 25%bv eq_refl ltac:(decLO_in) RK) R25).
assert (E26 : ew Em 26 = w64 pad) by exact (eq_trans (decLO_ek d regs2 regsc _ 26 26%bv eq_refl ltac:(decLO_in) RK) R26).
assert (E27 : ew Em 27 = w64 2) by exact (eq_trans (decLO_ek d regs2 regsc _ 27 27%bv eq_refl ltac:(decLO_in) RK) R27).
assert (E9u : ew Em 9 = Z_to_bv 64 q) by exact E9.
assert (E22u : ew Em 22 = Z_to_bv 64 n) by exact E22.
assert (E47 : ew Em 47 = Z_to_bv 64 (q + n)) by exact (decL_E_ex d regs2 _ 0).
assert (Hq0 : 4096 <= q) by (unfold HEAD in Q1; lia).
assert (HSm0 : st_ok tfibsegs Em decL_mss0
  (restrict (w_H Wc) (YK11.mkst regs2 (Z_to_bv 64 DEC_RA_MEMCHR) mem2 (YK11.seg_rom tfibsegs)))).
{ apply (decL_build B HSS d Wc lyc Sc Uc regs2 mem2 md2 k [Z_to_bv 64 (q + n)] DEC_RA_MEMCHR [decL_str] decL_mgf
    HE HJ2 HARU2).
  - unfold spZ. rewrite (RK 2%bv ltac:(decLO_in)). exact Hsp.
  - exact HFr2.
  - exact HLs2.
  - vm_compute. reflexivity.
  - apply (decLO_str_ok Em (w_H Wc) mem2 (q + n) E47u); [lia | lia | apply HQW; lia].
  - apply (decLO_mpd Em (d_sp d - DEC_F) (q + n) E2 E47u); [unfold DEC_F; lia | unfold DEC_F; lia | exact G1 | exact G2].
  - apply (decLO_mgf_ok Em q n (d_text d + Z.of_nat i) acc (6 * Z.of_nat (length six) mod 8) pad
      E8 E9 E18 E19 E20 E21 E22 E23 E24 E25 E26 E27 E47u Q1 Q16); unfold DEC_CEIL; lia. }
unfold decL_mss. refine (st_ok_facts tfibsegs Em decL_mss0 _ _ HSm0 _).
apply (facts_ok_add_alias Em (ss_facts decL_mss0)); [exact (st_ok_facts_ok tfibsegs _ _ _ HSm0)|].
rewrite (denot_lit_U Em (SAlu _ _ _)), (denot_lit_U Em (SOff 47 0)). f_equal.
rewrite U_SAlu. cbn [zalu_raw].
rewrite (U_atom Em 9 q E9u) by lia. rewrite (U_atom Em 22 n E22u) by lia.
rewrite (U_atom Em 47 (q + n) E47) by lia.
apply zcanon_small. lia.
Qed.

(* the shadow entry of the store byte q + n, from the block's range_addressable *)
Lemma decLO_msh_ok : forall d q i six pad acc Wc lyc Sc Uc regsc memc mdc k regs2 mem2,
  dec_entry_ok B d -> dec_head B d q i six pad acc Wc lyc Sc Uc regsc memc mdc k ->
  (i < length (d_tb d))%nat -> decL_memf B d q six Wc lyc Sc mem2 ->
  (forall r, In r decLO_kregs -> getr regs2 r = getr regsc r) ->
  sh_ok tfibsegs decL_Bx decL_mSH (decL_E d regs2 [Z_to_bv 64 (q + Z.of_nat (length (WriterSpec.six_bytes six)))])
    (mrestrict (w_H Wc) mem2).
Proof.
intros d q i six pad acc Wc lyc Sc Uc regsc memc mdc k regs2 mem2 HE HH Hilt HM2 RK.
pose proof asan_consts as ((C1 & C2) & _ & C4 & _).
destruct (decLO_mfacts d q i six pad acc Wc lyc Sc Uc regsc memc mdc k regs2 HE HH Hilt RK)
  as (_ & _ & _ & _ & Hnb & _).
pose proof (decLB_q B d q i six pad acc Wc lyc Sc Uc regsc memc mdc k HE HH) as (_ & Q1 & Q2 & _ & Qband & _).
destruct (decLO_hd d q i six pad acc Wc lyc Sc Uc regsc memc mdc k HH) as (_ & _ & _ & _ & _ & R21 & _).
assert (E21 : ew (decL_E d regs2 [Z_to_bv 64 (q + Z.of_nat (length (WriterSpec.six_bytes six)))]) 21 =
  Z_to_bv 64 SHADOW_OFF) by exact (eq_trans (decLO_ek d regs2 regsc _ 21 21%bv eq_refl ltac:(decLO_in) RK) R21).
assert (E47 : ew (decL_E d regs2 [Z_to_bv 64 (q + Z.of_nat (length (WriterSpec.six_bytes six)))]) 47 =
  Z_to_bv 64 (q + Z.of_nat (length (WriterSpec.six_bytes six)))) by exact (decL_E_ex d regs2 _ 0).
unfold HEAD in Q1.
unfold sh_ok, decL_mSH. constructor; [|constructor].
pose proof HM2 as (_ & HRA2 & _).
apply (shent_ok_of_range tfibsegs (w_H Wc) mem2 _ decL_Bx 47%nat q (d_n d)
  (q + Z.of_nat (length (WriterSpec.six_bytes six))) 0 1 HRA2).
- unfold decL_Bx. apply (U_atom _ 21 SHADOW_OFF E21). unfold SHADOW_OFF; lia.
- apply (U_atom _ 47 _ E47). lia.
- lia.
- lia.
- intros x Hx. rewrite C4 in Qband. unfold SHADOW_OFF in *. lia.
Qed.

(* ---- r = 0 (no letter): `beqz r` taken, to the call of fuzz_free ---- *)
Lemma decLT_none : forall d q i six pad acc Wc lyc Sc Uc regsc memc mdc k regs2 mem2 md2,
  dec_entry_ok B d -> dec_head B d q i six pad acc Wc lyc Sc Uc regsc memc mdc k ->
  (forall W3 ly3 S3 U3 regs3 mem3 md3 k3, dec_at_free B d q W3 ly3 S3 U3 regs3 mem3 md3 k3 ->
     SRr tfibsegs W3 (cfg_at tfibsegs A_fuzz_free regs3 mem3 md3) (dec_post B d)) ->
  (i < length (d_tb d))%nat ->
  WriterSpec.b64_ws (nth i (d_tb d) 0) = false -> nth i (d_tb d) 0 <> 61 -> WriterSpec.b64v (nth i (d_tb d) 0) = None ->
  dec_J B d lyc Sc Wc Uc mem2 md2 k -> ARU tfibsegs B lyc Sc Uc Wc mem2 md2 ->
  decL_memf B d q six Wc lyc Sc mem2 ->
  (forall r, In r decLO_kregs -> getr regs2 r = getr regsc r) ->
  st_ok tfibsegs (decL_E d regs2 [Z_to_bv 64 (q + Z.of_nat (length (WriterSpec.six_bytes six)))])
    (add_cond decL_mss (mkAC BC_EQ (SOff 10 0) (SLit 0)))
    (restrict (w_H Wc) (YK11.mkst regs2 (Z_to_bv 64 DEC_RA_MEMCHR) mem2 (YK11.seg_rom tfibsegs))) ->
  sh_ok tfibsegs decL_Bx decL_mSH (decL_E d regs2 [Z_to_bv 64 (q + Z.of_nat (length (WriterSpec.six_bytes six)))])
    (mrestrict (w_H Wc) mem2) ->
  SRr tfibsegs Wc (mkCfg (YK11.mkst regs2 (Z_to_bv 64 DEC_RA_MEMCHR) mem2 (YK11.seg_rom tfibsegs)) md2) (dec_post B d).
Proof.
intros d q i six pad acc Wc lyc Sc Uc regsc memc mdc k regs2 mem2 md2 HE HH HFREE Hilt Hws H61 Hv HJ2 HARU2 HM2 RK
  HS2 SHm.
destruct (decLO_mfacts d q i six pad acc Wc lyc Sc Uc regsc memc mdc k regs2 HE HH Hilt RK)
  as (E2 & E47u & SP2 & Htmp & _ & HD).
unfold dec_J in HJ2.
fsw_aj_run_to_tokU fsw_wr_tbl_ok HS2 HJ2 HARU2 SHm fs_Bspan A_fuzz_free.
{ eapply decLO_awr_m; [exact E2 | exact E47u | exact SP2 | exact Htmp | reflexivity]. }
apply (decLO_free d q i six pad acc Wc lyc Sc Uc regsc memc mdc k regs2 mem2 _ _ _ _ HE HH HFREE HM2 RK HS2
  ltac:(intros m Hm; rewrite ?ew_ewset_other by lia; reflexivity) eq_refl eq_refl eq_refl eq_refl HJ2 HARU2).
- exact (decLO_meq_m _ d _ _ mem2 mem2 _ E2 E47u HF (fun a _ _ _ => eq_refl) eq_refl).
- rewrite HD. exact (decLA_out_bad _ pad six _ Hws H61 Hv).
Qed.

(* ---- r = g_b64 + v (a letter): `beqz r` not taken, `bnez s10`, then the sextet ---- *)
Lemma decLT_some : forall d q i six pad acc Wc lyc Sc Uc regsc memc mdc k regs2 mem2 md2 v,
  dec_entry_ok B d -> dec_head B d q i six pad acc Wc lyc Sc Uc regsc memc mdc k ->
  (forall W3 ly3 S3 U3 regs3 mem3 md3 k3, dec_at_free B d q W3 ly3 S3 U3 regs3 mem3 md3 k3 ->
     SRr tfibsegs W3 (cfg_at tfibsegs A_fuzz_free regs3 mem3 md3) (dec_post B d)) ->
  (forall six' pad' acc' Wc' lyc' Sc' Uc' regsc' memc' mdc' k',
     dec_head B d q (S i) six' pad' acc' Wc' lyc' Sc' Uc' regsc' memc' mdc' k' ->
     SRr tfibsegs Wc' (mkCfg (YK11.mkst regsc' (Z_to_bv 64 DEC_HEAD) memc' (YK11.seg_rom tfibsegs)) mdc') (dec_post B d)) ->
  (i < length (d_tb d))%nat ->
  WriterSpec.b64_ws (nth i (d_tb d) 0) = false -> nth i (d_tb d) 0 <> 61 -> WriterSpec.b64v (nth i (d_tb d) 0) = Some v ->
  dec_J B d lyc Sc Wc Uc mem2 md2 k -> ARU tfibsegs B lyc Sc Uc Wc mem2 md2 ->
  decL_memf B d q six Wc lyc Sc mem2 ->
  (forall r, In r decLO_kregs -> getr regs2 r = getr regsc r) -> getr regs2 10 = w64 (G_B64 + v) ->
  st_ok tfibsegs (decL_E d regs2 [Z_to_bv 64 (q + Z.of_nat (length (WriterSpec.six_bytes six)))])
    (add_cond decL_mss (mkAC (neg_bc BC_EQ) (SOff 10 0) (SLit 0)))
    (restrict (w_H Wc) (YK11.mkst regs2 (Z_to_bv 64 DEC_RA_MEMCHR) mem2 (YK11.seg_rom tfibsegs))) ->
  sh_ok tfibsegs decL_Bx decL_mSH (decL_E d regs2 [Z_to_bv 64 (q + Z.of_nat (length (WriterSpec.six_bytes six)))])
    (mrestrict (w_H Wc) mem2) ->
  SRr tfibsegs Wc (mkCfg (YK11.mkst regs2 (Z_to_bv 64 DEC_RA_MEMCHR) mem2 (YK11.seg_rom tfibsegs)) md2) (dec_post B d).
Proof.
intros d q i six pad acc Wc lyc Sc Uc regsc memc mdc k regs2 mem2 md2 v HE HH HFREE HIH Hilt Hws H61 Hv HJ2 HARU2 HM2
  RK Rr HS2 SHm.
destruct (decLO_mfacts d q i six pad acc Wc lyc Sc Uc regsc memc mdc k regs2 HE HH Hilt RK)
  as (E2 & E47u & SP2 & Htmp & _ & HD).
pose proof HE as (_ & _ & _ & _ & _ & _ & _ & _ & HLEN & _).
destruct (decLO_hd d q i six pad acc Wc lyc Sc Uc regsc memc mdc k HH) as (_ & _ & Hpad & R24 & R26 & _ & _).
assert (E26 : ew (decL_E d regs2 [Z_to_bv 64 (q + Z.of_nat (length (WriterSpec.six_bytes six)))]) 26 = Z_to_bv 64 pad)
  by exact (eq_trans (decLO_ek d regs2 regsc _ 26 26%bv eq_refl ltac:(decLO_in) RK) R26).
assert (E24 : ew (decL_E d regs2 [Z_to_bv 64 (q + Z.of_nat (length (WriterSpec.six_bytes six)))]) 24 =
  Z_to_bv 64 (6 * Z.of_nat (length six) mod 8))
  by exact (eq_trans (decLO_ek d regs2 regsc _ 24 24%bv eq_refl ltac:(decLO_in) RK) R24).
pose proof (decLO_bits (Z.of_nat (length six)) ltac:(lia)) as (Hb1 & Hb2).
assert (Hp64 : 0 <= pad < 2 ^ 64) by lia.
clear R26 R24 HLEN.
unfold dec_J in HJ2.
(* 0x848fc -> 0x84900 *)
fsw_aj_run_tokU fsw_wr_tbl_ok HS2 HJ2 HARU2 SHm fs_Bspan.
{ eapply decLO_awr_m; [exact E2 | exact E47u | exact SP2 | exact Htmp | reflexivity]. }
pose proof (decLO_meq_m _ d _ _ mem2 mem2 _ E2 E47u HF (fun a _ _ _ => eq_refl) eq_refl) as MEQ3.
clear HF HFr HG.
(* 0x84900: bnez s10 *)
eapply SRr_sym_branch with (c := BC_NE) (a := SOff 26 0) (b := SLit 0); [exact HS2 | intros Hb' HS3 | intros Hb' HS3];
  rewrite (decLA_br_ne0 _ 26 pad E26 Hp64) in Hb'; clear HS2.
- (* pad <> 0: a letter after '=' *)
  apply Bool.negb_true_iff, Z.eqb_neq in Hb'.
  fsw_aj_run_to_tokU fsw_wr_tbl_ok HS3 HJ2 HARU2 SHm fs_Bspan A_fuzz_free.
  { eapply decLO_awr_m; [exact E2 | exact E47u | exact SP2 | exact Htmp | reflexivity]. }
  apply (decLO_free d q i six pad acc Wc lyc Sc Uc regsc memc mdc k regs2 mem2 _ _ _ _ HE HH HFREE HM2 RK HS3
    ltac:(intros m Hm; rewrite ?ew_ewset_other by lia; reflexivity) eq_refl eq_refl eq_refl eq_refl HJ2 HARU2).
  + exact (decLO_meq_m _ d _ _ mem2 _ _ E2 E47u HF MEQ3 eq_refl).
  + rewrite HD. exact (decLA_out_padbad _ _ pad six _ Hws H61 Hv Hb').
- (* pad = 0: the sextet is taken *)
  apply Bool.negb_false_iff, Z.eqb_eq in Hb'.
  destruct (decLA_bits_cases (Z.of_nat (length six)) ltac:(lia)) as [B0 | B26'].
  + (* bits = 0: no byte yet *)
    pose proof (decLO_add_atom _ _ _ 24 (mkAF 0 0 1) HS3
      ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2];
            rewrite E24, (unsigned_lit_small (6 * Z.of_nat (length six) mod 8)) by lia;
            change (2 ^ 1) with 2; lia)) as HS4.
    clear HS3.
    fsw_aj_run_to_tokU fsw_wr_tbl_ok HS4 HJ2 HARU2 SHm fs_Bspan DEC_HEAD.
    { eapply decLO_awr_m; [exact E2 | exact E47u | exact SP2 | exact Htmp | reflexivity]. }
    apply (decLO_next0 d q i six pad acc Wc lyc Sc Uc regsc memc mdc k regs2 mem2 v _ _ _ _ HE HH HIH
      Hilt Hws H61 Hv Hb' B0 HM2 RK Rr HS4
      ltac:(intros m Hm; rewrite ?ew_ewset_other by lia; reflexivity)
      eq_refl eq_refl eq_refl eq_refl HJ2 HARU2).
    exact (decLO_meq_m _ d _ _ mem2 _ _ E2 E47u HF MEQ3 eq_refl).
  + (* bits in [2, 6]: the byte q + n is stored *)
    assert (B26 : 2 <= 6 * Z.of_nat (length six) mod 8) by lia.
    pose proof (decLO_add_atom _ _ _ 24 (mkAF 2 6 1) HS3
      ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2];
            rewrite E24, (unsigned_lit_small (6 * Z.of_nat (length six) mod 8)) by lia;
            change (2 ^ 1) with 2; lia)) as HS4.
    clear HS3.
    fsw_aj_run_to_tokU fsw_wr_tbl_ok HS4 HJ2 HARU2 SHm fs_Bspan DEC_HEAD.
    { eapply decLO_awr_m; [exact E2 | exact E47u | exact SP2 | exact Htmp | reflexivity]. }
    apply (decLO_next2 d q i six pad acc Wc lyc Sc Uc regsc memc mdc k regs2 mem2 v _ _ _ _ HE HH HIH
      Hilt Hws H61 Hv Hb' B26 HM2 RK Rr HS4
      ltac:(intros m Hm; rewrite ?ew_ewset_other by lia; reflexivity)
      eq_refl eq_refl eq_refl eq_refl HJ2 HARU2).
    exact (decLO_meq_m _ d _ _ mem2 _ _ E2 E47u HF MEQ3 eq_refl).
Qed.

(* ---- the tail: memchr's result decides the arm ---- *)
Lemma decLO_tail : forall d q i six pad acc Wc lyc Sc Uc regsc memc mdc k regs2 mem2 md2 rv,
  dec_entry_ok B d -> dec_head B d q i six pad acc Wc lyc Sc Uc regsc memc mdc k ->
  (forall W3 ly3 S3 U3 regs3 mem3 md3 k3, dec_at_free B d q W3 ly3 S3 U3 regs3 mem3 md3 k3 ->
     SRr tfibsegs W3 (cfg_at tfibsegs A_fuzz_free regs3 mem3 md3) (dec_post B d)) ->
  (forall six' pad' acc' Wc' lyc' Sc' Uc' regsc' memc' mdc' k',
     dec_head B d q (S i) six' pad' acc' Wc' lyc' Sc' Uc' regsc' memc' mdc' k' ->
     SRr tfibsegs Wc' (mkCfg (YK11.mkst regsc' (Z_to_bv 64 DEC_HEAD) memc' (YK11.seg_rom tfibsegs)) mdc') (dec_post B d)) ->
  (i < length (d_tb d))%nat ->
  WriterSpec.b64_ws (nth i (d_tb d) 0) = false -> nth i (d_tb d) 0 <> 61 ->
  dec_J B d lyc Sc Wc Uc mem2 md2 k -> ARU tfibsegs B lyc Sc Uc Wc mem2 md2 ->
  decL_memf B d q six Wc lyc Sc mem2 ->
  dec_frame_ok Wc mem2 (d_sp d - DEC_F) (d_regs d) -> dec_lenp_slot Wc mem2 (d_sp d - DEC_F) (d_lenp d) ->
  (forall r, In r decLO_kregs -> getr regs2 r = getr regsc r) ->
  getr regs2 10 = w64 rv ->
  match zfind (nth i (d_tb d) 0) WriterSpec.b64_table with None => rv = 0 | Some j => rv = G_B64 + Z.of_nat j end ->
  SRr tfibsegs Wc (mkCfg (YK11.mkst regs2 (Z_to_bv 64 DEC_RA_MEMCHR) mem2 (YK11.seg_rom tfibsegs)) md2) (dec_post B d).
Proof.
intros d q i six pad acc Wc lyc Sc Uc regsc memc mdc k regs2 mem2 md2 rv HE HH HFREE HIH Hilt Hws H61 HJ2 HARU2 HM2
  HFr2 HLs2 RK Rr Hz.
pose proof (decLO_mss_ok d q i six pad acc Wc lyc Sc Uc regsc memc mdc k regs2 mem2 md2 HE HH Hilt HJ2 HARU2 HFr2 HLs2 RK)
  as HSm.
pose proof (decLO_msh_ok d q i six pad acc Wc lyc Sc Uc regsc memc mdc k regs2 mem2 HE HH Hilt HM2 RK) as SHm.
assert (E10 : ew (decL_E d regs2 [Z_to_bv 64 (q + Z.of_nat (length (WriterSpec.six_bytes six)))]) 10 = Z_to_bv 64 rv)
  by (rewrite (decL_E_reg d regs2 _ 10 10%bv eq_refl); exact Rr).
pose proof (decLA_zfind (nth i (d_tb d) 0) (decLO_c d i HE Hilt)) as Zf.
revert Hz Zf. destruct (zfind (nth i (d_tb d) 0) WriterSpec.b64_table) as [j|] eqn:Ez; intros Hz Zf; subst rv.
- pose proof (decLA_b64v_range _ _ Zf) as Hj.
  eapply SRr_sym_branch with (c := BC_EQ) (a := SOff 10 0) (b := SLit 0); [exact HSm | intros Hb _ | intros _ HS2].
  + exfalso. rewrite (decLA_br_eq0 _ 10 (G_B64 + Z.of_nat j) E10 ltac:(unfold G_B64; lia)) in Hb.
    apply Z.eqb_eq in Hb. unfold G_B64 in Hb. lia.
  + exact (decLT_some d q i six pad acc Wc lyc Sc Uc regsc memc mdc k regs2 mem2 md2 (Z.of_nat j) HE HH HFREE HIH Hilt
      Hws H61 Zf HJ2 HARU2 HM2 RK Rr HS2 SHm).
- eapply SRr_sym_branch with (c := BC_EQ) (a := SOff 10 0) (b := SLit 0); [exact HSm | intros _ HS2 | intros Hb _].
  + exact (decLT_none d q i six pad acc Wc lyc Sc Uc regsc memc mdc k regs2 mem2 md2 HE HH HFREE Hilt Hws H61 Zf
      HJ2 HARU2 HM2 RK HS2 SHm).
  + exfalso. rewrite (decLA_br_eq0 _ 10 0 E10 ltac:(lia)) in Hb. cbn in Hb. discriminate Hb.
Qed.

(* ==== the head side: from the head 0x848bc to the call of memchr at PC_memchr, the call, and the return ==== *)
(* the head facts the call reads *)
Lemma decLO_hd2 : forall d q i six pad acc Wc lyc Sc Uc regsc memc mdc k,
  dec_head B d q i six pad acc Wc lyc Sc Uc regsc memc mdc k ->
  dec_J B d lyc Sc Wc Uc memc mdc k /\ ARU tfibsegs B lyc Sc Uc Wc memc mdc /\
  getr regsc 3 = getr (d_regs d) 3 /\ getr regsc 4 = getr (d_regs d) 4 /\ getr regsc 8 = w64 DEC_WSMASK /\
  getr regsc 19 = w64 G_B64 /\ getr regsc 25 = w64 61.
Proof.
intros d q i six pad acc Wc lyc Sc Uc regsc memc mdc k HH. decL_unhead HH.
exact (conj HJ (conj HARU (conj R3 (conj R4 (conj R8 (conj R19 R25)))))).
Qed.

(* the call of memchr (g_b64, c, 65) from the engine's state at PC_memchr (regs decLO_cregs, the head's regions), the
   interceptor's contract HMEMCHR, the journal put back over the return (fsw_intrin_atU), then decLO_tail at 0x848fc *)
Lemma decLO_call : forall d q i six pad acc Wc lyc Sc Uc regsc memc mdc k Ex ss ms md',
  dec_entry_ok B d -> dec_head B d q i six pad acc Wc lyc Sc Uc regsc memc mdc k ->
  (forall W3 ly3 S3 U3 regs3 mem3 md3 k3, dec_at_free B d q W3 ly3 S3 U3 regs3 mem3 md3 k3 ->
     SRr tfibsegs W3 (cfg_at tfibsegs A_fuzz_free regs3 mem3 md3) (dec_post B d)) ->
  (forall six' pad' acc' Wc' lyc' Sc' Uc' regsc' memc' mdc' k',
     dec_head B d q (S i) six' pad' acc' Wc' lyc' Sc' Uc' regsc' memc' mdc' k' ->
     SRr tfibsegs Wc' (mkCfg (YK11.mkst regsc' (Z_to_bv 64 DEC_HEAD) memc' (YK11.seg_rom tfibsegs)) mdc') (dec_post B d)) ->
  (i < length (d_tb d))%nat ->
  WriterSpec.b64_ws (nth i (d_tb d) 0) = false -> nth i (d_tb d) 0 <> 61 ->
  st_ok tfibsegs Ex ss (restrict (w_H Wc) ms) ->
  (forall n, (n < 48)%nat -> ew Ex n = ew (decL_E d regsc [Z_to_bv 64 (nth i (d_tb d ++ [0]) 0)]) n) ->
  ss_pc ss = PC_memchr -> ss_resv ss = None -> ss_regs ss = decLO_cregs ->
  ss_mem ss = fsT_ret_regions DEC_F decL_cs [decL_txr] ->
  dec_J B d lyc Sc Wc Uc (ms_mem ms) md' k -> ARU tfibsegs B lyc Sc Uc Wc (ms_mem ms) md' ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (d_sp d - DEC_F <= a < d_sp d) -> ms_mem ms (Z_to_bv 64 a) = memc (Z_to_bv 64 a)) ->
  SRr tfibsegs Wc (mkCfg ms md') (dec_post B d).
Proof.
intros d q i six pad acc Wc lyc Sc Uc regsc memc mdc k Ex ss ms md' HE HH HFREE HIH Hilt Hws H61 HS HEx Hpc Hrv Hregs
  Hmem HJ HARU MEQ.
pose proof asan_consts as ((C1 & C2) & _ & _ & _ & C5).
assert (FR : STK_RT_STR = ltac:(let v := eval vm_compute in STK_RT_STR in exact v)) by reflexivity.
assert (FE : ESTACK = 4096) by reflexivity.
assert (FS : STK_preset_base64_decode = ltac:(let v := eval vm_compute in STK_preset_base64_decode in exact v)) by reflexivity.
assert (Hcn : nth i (d_tb d ++ [0]) 0 = nth i (d_tb d) 0) by (rewrite app_nth1 by exact Hilt; reflexivity).
rewrite Hcn in HEx.
pose proof (decLO_c d i HE Hilt) as Hc.
destruct (decLO_hd d q i six pad acc Wc lyc Sc Uc regsc memc mdc k HH) as (Hsp & _).
destruct (decLO_hd2 d q i six pad acc Wc lyc Sc Uc regsc memc mdc k HH) as (_ & _ & R3 & R4 & _ & R19 & _).
pose proof (fsw_sp B _ _ _ _ _ _ _ _ _ (proj1 (proj1 HE))) as (Hsp16 & Hspc & Hsp47 & _).
change (spZ (d_regs d)) with (d_sp d) in Hsp16, Hspc, Hsp47.
pose proof (decLB_sp B d HE) as (SP1 & SP2 & SP3).
pose proof (decL_lenp_range B d HE) as (L1 & L2 & _).
pose proof (proj1 (proj1 HE)) as HPREU. pose proof HPREU as (HAP & _ & _).
pose proof HAP as (_ & _ & _ & Hgp & Htp & _).
pose proof HE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPL).
assert (Hot16 : d_ot d mod 16 = 0).
{ destruct HPL as [(_ & _ & _ & H & _) | (_ & H & _)]; [exact H | rewrite H; exact Hsp16]. }
clear HPL HAP HPREU.
(* ---- the registers at the call ---- *)
assert (GK : forall (r : bv 5) (m : nat), sr_get decLO_cregs r = SOff m 0 -> (m < 48)%nat -> Z.of_nat m = bv_unsigned r ->
  getr (ms_regs ms) r = getr regsc r).
{ intros r m H1 Hm Hr. apply (decL_reg (w_H Wc) Ex ss ms r (SOff m 0)); [exact HS | rewrite Hregs; exact H1 |].
  rewrite fsw_SOff0, (HEx m Hm). exact (decL_E_reg d regsc _ m r Hr). }
assert (R1 : getr (ms_regs ms) 1 = Z_to_bv 64 542972)
  by exact (fsw_reg_lit (w_H Wc) Ex ss ms 1%bv 542972 HS ltac:(rewrite Hregs; reflexivity) ltac:(lia)).
assert (R12 : getr (ms_regs ms) 12 = Z_to_bv 64 65)
  by exact (fsw_reg_lit (w_H Wc) Ex ss ms 12%bv 65 HS ltac:(rewrite Hregs; reflexivity) ltac:(lia)).
assert (R10 : getr (ms_regs ms) 10 = w64 G_B64).
{ apply (decL_reg (w_H Wc) Ex ss ms 10%bv (SOff 19 0)); [exact HS | rewrite Hregs; reflexivity |].
  rewrite fsw_SOff0, (HEx 19%nat ltac:(lia)), (decL_E_reg d regsc _ 19 19%bv eq_refl). exact R19. }
assert (R11 : getr (ms_regs ms) 11 = w64 (nth i (d_tb d) 0)).
{ apply (decL_reg (w_H Wc) Ex ss ms 11%bv (SOff 47 0)); [exact HS | rewrite Hregs; reflexivity |].
  rewrite fsw_SOff0, (HEx 47%nat ltac:(lia)). exact (decL_E_ex d regsc _ 0). }
assert (R2 : getr (ms_regs ms) 2 = getr regsc 2) by (apply (GK 2%bv 2%nat); [vm_compute; reflexivity | lia | reflexivity]).
assert (R3m : getr (ms_regs ms) 3 = getr regsc 3) by (apply (GK 3%bv 3%nat); [vm_compute; reflexivity | lia | reflexivity]).
assert (R4m : getr (ms_regs ms) 4 = getr regsc 4) by (apply (GK 4%bv 4%nat); [vm_compute; reflexivity | lia | reflexivity]).
assert (Hspt : spZ (ms_regs ms) = d_sp d - DEC_F) by (unfold spZ at 1; rewrite R2; exact Hsp).
(* ---- the call's precondition and memchr's premises ---- *)
unfold dec_J in HJ.
assert (HPRE1 : ecall_preU_k tfibsegs B STK_RT_STR lyc Sc Uc Wc (ms_regs ms) (ms_mem ms) md').
{ apply (fsw_ecall_preU_k_at B (d_STKJ d) (d_ot d) (d_FP d) (d_ly d) (d_S d) (d_W d) (unpoison (d_U d) (d_mem d))
    (d_md d) [] lyc Sc Uc Wc (ms_mem ms) md' k (ms_regs ms) (d_sp d - DEC_F - d_ot d) STK_RT_STR HJ HARU).
  - rewrite Hspt. lia.
  - unfold DEC_F. lia.
  - unfold DEC_F. lia.
  - rewrite FE. unfold d_STKJ, DEC_F. rewrite FS. lia.
  - rewrite FR. lia.
  - rewrite FR. unfold d_STKJ, DEC_F. rewrite FS. lia.
  - rewrite R1. apply ret_ok_even. rewrite unsigned_lit_small by lia. reflexivity.
  - rewrite R3m, R3. exact Hgp.
  - rewrite R4m, R4. exact Htp. }
assert (AGR : forall a, 0 <= a < 2 ^ 64 -> ~ (d_sp d - DEC_F <= a < d_sp d) ->
  aview tfibsegs (w_H Wc) (ms_mem ms) a = aview tfibsegs (w_H Wc) memc a)
  by (intros a Ha Hn; apply aview_at; exact (MEQ a Ha Hn)).
destruct (decLB_g64 B HIMG d q i six pad acc Wc lyc Sc Uc regsc memc mdc k (ms_mem ms) (d_sp d - DEC_F) (d_sp d)
  HE HH ltac:(unfold DEC_F in *; lia) ltac:(lia) AGR) as (HROM & HZB & HRA & HHV).
pose proof (decLO_mchr (nth i (d_tb d) 0) ltac:(lia)) as Hml.
assert (HRAm : range_addressable (aview tfibsegs (w_H Wc) (ms_mem ms)) SHADOW_OFF G_B64
  (mchr_len (nth i (d_tb d) 0) WriterSpec.b64_table)) by (intros x Hx; apply HRA; lia).
assert (HHVm : shadow_hull_vis (aview tfibsegs (w_H Wc) (ms_mem ms)) G_B64
  (mchr_len (nth i (d_tb d) 0) WriterSpec.b64_table)) by exact (decLO_hull_sub _ G_B64 65 _ Hml HHV).
assert (Hamem : amem_range G_B64 (65 + 8)) by (unfold amem_range; left; rewrite C5; unfold G_B64; lia).
assert (Hlen65 : Z.of_nat (length WriterSpec.b64_table) = 65) by (vm_compute; reflexivity).
pose proof HARU as (_ & HUOK & _).
(* ---- the call ---- *)
rewrite (st_ok_restrict_mkst tfibsegs (w_H Wc) Ex ss ms HS Hrv), Hpc.
eapply SRr_bind.
{ apply (fsw_intrin_atU B (d_STKJ d) (d_ot d) (d_FP d) (d_ly d) (d_S d) (d_W d) (unpoison (d_U d) (d_mem d)) (d_md d)
    [] lyc Sc Uc Wc (ms_mem ms) md' k Uc (fun a => spZ (ms_regs ms) - STK_RT_STR <= a < spZ (ms_regs ms))
    (Z_to_bv 64 DEC_RA_MEMCHR) _
    (fun regs2 mem2 md2 => aregs_preserved (ms_regs ms) regs2 /\
       (exists v, getr regs2 10 = w64 v /\
          match zfind (nth i (d_tb d) 0) WriterSpec.b64_table with None => v = 0 | Some j => v = G_B64 + Z.of_nat j end) /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ (ms_regs ms) - STK_RT_STR <= a < spZ (ms_regs ms)) ->
          aview tfibsegs (w_H Wc) mem2 a = aview tfibsegs (w_H Wc) (ms_mem ms) a)) HJ).
  - eapply SRr_mono;
      [exact (HMEMCHR lyc Sc Uc Wc (ms_regs ms) (ms_mem ms) md' G_B64 (nth i (d_tb d) 0) 65 WriterSpec.b64_table
         HPRE1 HROM R10 R11 ltac:(lia) R12 ltac:(lia) HZB Hlen65 ltac:(unfold G_B64; lia) ltac:(unfold G_B64; lia)
         Hamem HRAm (fun _ => HHVm))|].
    intros W2 c2 _ (EW & regs2 & mem2 & md2 & v0 & Ec & HAR2 & PO2 & HP2 & Hsame & H10v & Hv0 & HR & Hfr & Hgr).
    split; [exact EW|]. exists regs2, mem2, md2.
    split.
    { rewrite Ec. unfold cfg_at, raZ, w64. rewrite R1, unsigned_lit_small by lia. reflexivity. }
    split; [split; [exact HAR2 | split; [exact HUOK | exact PO2]]|].
    split; [exact Hsame|].
    split.
    { intros a Ha Hn. destruct (in_ush Uc (bv_unsigned (Z_to_bv 64 a))) eqn:Eu.
      - apply (aview_unpoison_in tfibsegs). exact Eu.
      - rewrite (aview_unpoison_out tfibsegs (w_H Wc) Uc mem2 a Eu),
          (aview_unpoison_out tfibsegs (w_H Wc) Uc (ms_mem ms) a Eu).
        exact (Hfr a Ha Hn). }
    split.
    { intros a (Hh & b & Hb). split; [exact Hh|]. unfold unpoison in Hb |- *.
      destruct (in_ush Uc (bv_unsigned (Z_to_bv 64 a))); [eexists; reflexivity|].
      destruct (Hgr a (conj Hh (ex_intro _ b Hb))) as (_ & b' & Hb'). exists b'. exact Hb'. }
    split; [exact HP2|]. split; [exists v0; split; [exact H10v | exact HR]|]. exact Hfr.
  - intros a Ha. left; left. rewrite Hspt, FR in Ha. unfold d_STKJ, DEC_F in *. rewrite FS. lia. }
intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HARU2 & HP2 & (v & H10 & Hv) & Hfr2).
(* ---- the return at 0x848fc: the loop facts back over the new memory ---- *)
assert (Hlo : alloc_ceiling <= d_sp d - DEC_F - 8192) by (unfold DEC_F; rewrite FS in Hspc; lia).
assert (AG2 : forall a, 0 <= a < 2 ^ 64 -> ~ (d_sp d - DEC_F - 8192 <= a < d_sp d) ->
  aview tfibsegs (w_H Wc) mem2 a = aview tfibsegs (w_H Wc) memc a).
{ intros a Ha Hn. rewrite (Hfr2 a Ha ltac:(rewrite Hspt, FR; unfold DEC_F in *; lia)).
  apply AGR; [exact Ha | unfold DEC_F in *; lia]. }
pose proof (decLB_keep B d q i six pad acc Wc lyc Sc Uc regsc memc mdc k memc mem2 (d_sp d - DEC_F - 8192) (d_sp d)
  HE HH (decLB_memf B d q i six pad acc Wc lyc Sc Uc regsc memc mdc k HH) Hlo ltac:(lia) AG2) as HM2.
assert (E2x : bv_unsigned (ew Ex 2) = d_sp d - DEC_F)
  by (rewrite (HEx 2%nat ltac:(lia)), (decL_E_reg d regsc _ 2 2%bv eq_refl); exact Hsp).
destruct (decL_frame_back d regsc [Z_to_bv 64 (nth i (d_tb d) 0)] Wc ms Ex ss HS ltac:(rewrite Hmem; reflexivity) E2x
  (fun n Hn => HEx n ltac:(lia)) ltac:(lia)) as (HFr1 & HLs1).
assert (HFr2 : dec_frame_ok Wc mem2 (d_sp d - DEC_F) (d_regs d)).
{ intros j r Hj. assert (Hj13 : (j < length dec_saved)%nat) by (apply nth_error_Some; rewrite Hj; discriminate).
  cbv [dec_saved length] in Hj13.
  apply (decLB_val_mem (w_H Wc) (ms_mem ms) mem2 _ 8); [|exact (HFr1 j r Hj)].
  intros kk Hk. apply Hfr2; [|rewrite Hspt, FR]; unfold DEC_F in *; lia. }
assert (HLs2 : dec_lenp_slot Wc mem2 (d_sp d - DEC_F) (d_lenp d)).
{ unfold dec_lenp_slot in *.
  apply (decLB_val_mem (w_H Wc) (ms_mem ms) mem2 _ 8); [|exact HLs1].
  intros kk Hk. apply Hfr2; [|rewrite Hspt, FR]; unfold DEC_F in *; lia. }
assert (RK : forall r, In r decLO_kregs -> getr regs2 r = getr regsc r).
{ intros r Hr. cbv [decLO_kregs In] in Hr. repeat (destruct Hr as [<-|Hr]); [..|destruct Hr];
  rewrite (fsw_pres _ _ _ HP2) by decLO_cs;
  lazymatch goal with |- getr _ ?r = _ =>
    let n := eval vm_compute in (Z.to_nat (bv_unsigned r)) in
    apply (GK r n); [vm_compute; reflexivity | lia | reflexivity] end. }
exact (decLO_tail d q i six pad acc Wc lyc Sc Uc regsc memc mdc k regs2 mem2 md2 v HE HH HFREE HIH Hilt Hws H61 HJ2
  HARU2 HM2 HFr2 HLs2 RK H10 Hv).
Qed.

(* ==== decL_arm_other: one iteration on a byte that is not whitespace, not '=' and not the NUL (contract
   (internal path), verbatim). From the head: `bltu s9, c` (0x848d0); c > 61 runs to PC_memchr; c <= 61 passes
   the whitespace test (0x848dc, not taken), `c <> 61` (0x848e0, taken) and `c == 0` (0x848ec, not taken) to
   PC_memchr; then decLO_call ==== *)
Lemma decL_arm_other : forall d q i six pad acc Wc lyc Sc Uc regsc memc mdc k,
  dec_entry_ok B d -> dec_head B d q i six pad acc Wc lyc Sc Uc regsc memc mdc k ->
  (forall W3 ly3 S3 U3 regs3 mem3 md3 k3, dec_at_free B d q W3 ly3 S3 U3 regs3 mem3 md3 k3 ->
     SRr tfibsegs W3 (cfg_at tfibsegs A_fuzz_free regs3 mem3 md3) (dec_post B d)) ->
  (forall six' pad' acc' Wc' lyc' Sc' Uc' regsc' memc' mdc' k',
     dec_head B d q (S i) six' pad' acc' Wc' lyc' Sc' Uc' regsc' memc' mdc' k' ->
     SRr tfibsegs Wc' (mkCfg (YK11.mkst regsc' (Z_to_bv 64 DEC_HEAD) memc' (YK11.seg_rom tfibsegs)) mdc') (dec_post B d)) ->
  (i < length (d_tb d))%nat ->
  WriterSpec.b64_ws (nth i (d_tb d) 0) = false -> nth i (d_tb d) 0 <> 61 ->
  SRr tfibsegs Wc (mkCfg (YK11.mkst regsc (Z_to_bv 64 DEC_HEAD) memc (YK11.seg_rom tfibsegs)) mdc) (dec_post B d).
Proof.
intros d q i six pad acc Wc lyc Sc Uc regsc memc mdc k HE HH HFREE HIH Hilt Hws H61.
destruct (decL_head_st B HSS (decLB_text B) (decLB_q B) d q i six pad acc Wc lyc Sc Uc regsc memc mdc k HE HH)
  as [HS SHOK].
pose proof (decLO_c d i HE Hilt) as Hc.
destruct (decLO_hd d q i six pad acc Wc lyc Sc Uc regsc memc mdc k HH) as (Hsp & _).
destruct (decLO_hd2 d q i six pad acc Wc lyc Sc Uc regsc memc mdc k HH) as (HJ & HARU & _ & _ & R8 & _ & R25).
pose proof (decLB_sp B d HE) as (_ & SP2 & _).
assert (E2 : bv_unsigned (ew (decL_E d regsc [Z_to_bv 64 (nth i (d_tb d ++ [0]) 0)]) 2) = d_sp d - DEC_F)
  by (rewrite (decL_E_reg d regsc _ 2 2%bv eq_refl); exact Hsp).
assert (E8 : ew (decL_E d regsc [Z_to_bv 64 (nth i (d_tb d ++ [0]) 0)]) 8 = Z_to_bv 64 DEC_WSMASK)
  by (rewrite (decL_E_reg d regsc _ 8 8%bv eq_refl); exact R8).
assert (E25 : ew (decL_E d regsc [Z_to_bv 64 (nth i (d_tb d ++ [0]) 0)]) 25 = Z_to_bv 64 61)
  by (rewrite (decL_E_reg d regsc _ 25 25%bv eq_refl); exact R25).
assert (E47 : ew (decL_E d regsc [Z_to_bv 64 (nth i (d_tb d ++ [0]) 0)]) 47 = Z_to_bv 64 (nth i (d_tb d) 0)).
{ rewrite <- (app_nth1 (d_tb d) [0] 0 Hilt). exact (decL_E_ex d regsc _ 0). }
clear R8 R25.
unfold dec_J in HJ.
(* 0x848bc -> 0x848d0 *)
fsw_aj_run_tokU fsw_wr_tbl_ok HS HJ HARU SHOK fs_Bspan.
{ eapply decLO_awr_h; [exact E2 | exact SP2 | reflexivity]. }
pose proof (decLO_meq_h _ d _ memc _ _ HF ltac:(rewrite ?ew_ewset_other by lia; exact E2) (fun a _ _ => eq_refl)
  eq_refl) as MEQ.
clear HF HFr HG.
(* 0x848d0: bltu s9, c *)
eapply SRr_sym_branch with (c := BC_LTU) (a := SOff 25 0) (b := SOff 47 0); [exact HS | intros Hb HS2 | intros Hb HS2];
  rewrite (decLA_br_ltu _ 25 47 61 (nth i (d_tb d) 0)) in Hb
    by (rewrite ?ew_ewset_other by lia; first [exact E25 | exact E47 | lia]);
  clear HS.
- (* 61 < c: to PC_memchr *)
  fsw_aj_run_to_tokU fsw_wr_tbl_ok HS2 HJ HARU SHOK fs_Bspan PC_memchr.
  { eapply decLO_awr_h; [rewrite ?ew_ewset_other by lia; exact E2 | exact SP2 | reflexivity]. }
  apply (decLO_call d q i six pad acc Wc lyc Sc Uc regsc memc mdc k _ _ _ _ HE HH HFREE HIH Hilt Hws H61 HS2
    ltac:(intros m Hm; rewrite ?ew_ewset_other by lia; reflexivity) eq_refl eq_refl eq_refl eq_refl HJ HARU).
  exact (decLO_meq_h _ d _ memc _ _ HF ltac:(rewrite ?ew_ewset_other by lia; exact E2) MEQ eq_refl).
- (* c <= 61 *)
  apply Z.ltb_ge in Hb.
  fsw_aj_run_tokU fsw_wr_tbl_ok HS2 HJ HARU SHOK fs_Bspan.
  { eapply decLO_awr_h; [rewrite ?ew_ewset_other by lia; exact E2 | exact SP2 | reflexivity]. }
  pose proof (decLO_meq_h _ d _ memc _ _ HF ltac:(rewrite ?ew_ewset_other by lia; exact E2) MEQ eq_refl) as MEQ2.
  clear HF HFr HG MEQ.
  (* 0x848dc: (mask >> c) & 1, not taken: c is no whitespace *)
  eapply SRr_sym_branch with (c := BC_NE) (a := SAlu ALU_AND (SAlu ALU_SRL (SOff 8 0) (SOff 47 0)) (SLit 1))
    (b := SLit 0); [exact HS2 | intros Hb2 HS3 | intros Hb2 HS3];
    rewrite (decLA_br_ws _ 8 47 (nth i (d_tb d) 0)) in Hb2
      by (rewrite ?ew_ewset_other by lia; first [exact E8 | exact E47 | lia]);
    clear HS2.
  + exfalso. rewrite Hws in Hb2. discriminate Hb2.
  + fsw_aj_run_tokU fsw_wr_tbl_ok HS3 HJ HARU SHOK fs_Bspan.
    { eapply decLO_awr_h; [rewrite ?ew_ewset_other by lia; exact E2 | exact SP2 | reflexivity]. }
    pose proof (decLO_meq_h _ d _ memc _ _ HF ltac:(rewrite ?ew_ewset_other by lia; exact E2) MEQ2 eq_refl) as MEQ3.
    clear HF HFr HG MEQ2.
    (* 0x848e0: c <> 61, taken *)
    eapply SRr_sym_branch with (c := BC_NE) (a := SOff 47 0) (b := SOff 25 0); [exact HS3 | intros Hb3 HS4 | intros Hb3 HS4];
      rewrite (decLA_br_ne _ 47 25 (nth i (d_tb d) 0) 61) in Hb3
        by (rewrite ?ew_ewset_other by lia; first [exact E47 | exact E25 | lia]);
      clear HS3.
    * fsw_aj_run_tokU fsw_wr_tbl_ok HS4 HJ HARU SHOK fs_Bspan.
      { eapply decLO_awr_h; [rewrite ?ew_ewset_other by lia; exact E2 | exact SP2 | reflexivity]. }
      pose proof (decLO_meq_h _ d _ memc _ _ HF ltac:(rewrite ?ew_ewset_other by lia; exact E2) MEQ3 eq_refl) as MEQ4.
      clear HF HFr HG MEQ3.
      (* 0x848ec: c == 0, not taken *)
      eapply SRr_sym_branch with (c := BC_EQ) (a := SOff 47 0) (b := SLit 0); [exact HS4 | intros Hb4 HS5 | intros Hb4 HS5];
        rewrite (decLA_br_eq0 _ 47 (nth i (d_tb d) 0)) in Hb4
          by (rewrite ?ew_ewset_other by lia; first [exact E47 | lia]);
        clear HS4.
      -- exfalso. apply Z.eqb_eq in Hb4. lia.
      -- fsw_aj_run_to_tokU fsw_wr_tbl_ok HS5 HJ HARU SHOK fs_Bspan PC_memchr.
         { eapply decLO_awr_h; [rewrite ?ew_ewset_other by lia; exact E2 | exact SP2 | reflexivity]. }
         apply (decLO_call d q i six pad acc Wc lyc Sc Uc regsc memc mdc k _ _ _ _ HE HH HFREE HIH Hilt Hws H61 HS5
           ltac:(intros m Hm; rewrite ?ew_ewset_other by lia; reflexivity) eq_refl eq_refl eq_refl eq_refl HJ HARU).
         exact (decLO_meq_h _ d _ memc _ _ HF ltac:(rewrite ?ew_ewset_other by lia; exact E2) MEQ4 eq_refl).
    * exfalso. apply Bool.negb_false_iff, Z.eqb_eq in Hb3. exact (H61 Hb3).
Qed.

End L4.
