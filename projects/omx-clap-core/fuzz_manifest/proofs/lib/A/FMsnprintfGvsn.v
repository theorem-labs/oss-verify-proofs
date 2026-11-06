(* musl vsnprintf 0x91f0c (fm.asan) in the donor's proof form, from the contracts of __wrap_memset and
   __interceptor_vfprintf: entry at sp0 + 0x160 (s = D, n = N, fmt, ap = P), frame 0x130 with the stack protector,
   memset (sp, 0, 0xe8) through __wrap_memset 0x51a60 (ra 0x91f70), the FILE fields, the cookie {D, N - 1}, *D = 0,
   __wrap_vfprintf 0x41308 = j 0x457ec (ra 0x91fac) with the FILE at sp0 + FO, the canary check and the epilogue.
   New file. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0k YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP04 YP0g YP01.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG0v YO0f.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC20 YI00 YI16 YK06.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import AB1v AE34 AF0l AF0m AF0x AE20 AE2y.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMupoison FMH_Base FMH_Rt FMsnprintfI FMsnprintfK.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMsnprintfGI FMsnprintfGk FMsnprintfGt.
Import ListNotations.
Open Scope Z_scope.

(* ---- the walk's symbolic states and runs. Atom 2 = the entry sp sp0 + 0x160, atoms 0..31 the entry registers,
   atom 32 the canary value; the stack region spans the band below the entry sp (the callees' bands lie in it) ---- *)
Section r. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition gvK : Z := SNK_STK + 0x160.
Definition gv_stk0 : YP09.region := YP09.mkRegion (Some 2%nat) (- gvK) 0 (- gvK) 0 [].
Definition gv_got : YP09.region :=
  YP09.mkRegion None FM_GOT_canary (FM_GOT_canary + 8) 0 0 [YP09.mkChunk FM_GOT_canary (CVal 8 (SLit FM_canary))].
Definition gv_can : YP09.region :=
  YP09.mkRegion None FM_canary (FM_canary + 8) 0 0 [YP09.mkChunk FM_canary (CVal 8 (SOff 32 0))].
(* sp0 + 0x160 is 16-aligned in [2^44, 2^47]; 1 <= N <= 2^30 decides `beqz a1` and folds c.n to N - 1 *)
Definition gv_facts : facts := mkFacts [(2%nat, mkAF (2 ^ 44) (2 ^ 47) 4); (11%nat, mkAF 1 (2 ^ 30) 0)] [] [].
Definition gv_s0 : sstate := mkSS A_VSN sr_atoms [gv_stk0; gv_got; gv_can] None gv_facts.
Definition GVTO (stop : Z) (s : sstate) := sym_run_toN tfibsegs tbl_g FUEL stop s.
Definition GVRUN (s : sstate) := sym_runN tfibsegs tbl_g FUEL s.
(* entry to the memset call: frame, canary copy, cookie {D, N - 1} at sp + 0xe8 *)
Definition gv_e1 : sstate := Eval vm_compute in fst (GVTO W_MEMSET gv_s0).
Lemma r_gv1 : GVTO W_MEMSET gv_s0 = (gv_e1, RS_running). Proof. vm_compute. reflexivity. Qed.
Definition gv_e1r : YP09.region := Eval vm_compute in hd gv_stk0 (ss_mem gv_e1).
Lemma gv_e1_mem : ss_mem gv_e1 = [gv_e1r] ++ gv_got :: [gv_can]. Proof. vm_compute. reflexivity. Qed.
(* the GOT slot is read once; it is dropped before the calls *)
Definition gv_e1d : sstate := set_mem gv_e1 ([gv_e1r] ++ [gv_can]).
(* after memset: the caller-saved registers havoc'd from atom 33, the zeros back as a CZero chunk *)
Definition gv_k1 : sstate := kafter 33 gv_e1d RA_MSET (-304) (-304) (-72).
Definition gv_k1r : YP09.region := Eval vm_compute in hd gv_stk0 (ss_mem gv_k1).
Lemma gv_k1_mem : ss_mem gv_k1 = gv_k1r :: [gv_can]. Proof. vm_compute. reflexivity. Qed.
Definition gv_zc : YP09.chunk := YP09.mkChunk (-304) (CZero 232).
Definition gv_addc (r : YP09.region) (c : YP09.chunk) : YP09.region :=
  YP09.mkRegion (YP09.r_base r) (YP09.r_lo r) (YP09.r_hi r) (YP09.r_wlo r) (YP09.r_whi r) (c :: YP09.r_chunks r).
Definition gv_s2 : sstate := set_mem gv_k1 (gv_addc gv_k1r gv_zc :: [gv_can]).
(* the FILE stores, up to `sb zero, 0(s3)` (s3 = D, outside every region) *)
Definition gv_e3 : sstate := Eval vm_compute in fst (GVTO A_VFPI gv_s2).
Lemma r_gv3 : GVTO A_VFPI gv_s2 = (gv_e3, RS_stopped (SR_store (Some 10%nat) 0)). Proof. vm_compute. reflexivity. Qed.
Definition gv_e3r : YP09.region := Eval vm_compute in hd gv_stk0 (ss_mem gv_e3).
Lemma gv_e3_mem : ss_mem gv_e3 = gv_e3r :: [gv_can]. Proof. vm_compute. reflexivity. Qed.
Definition gv_s3 : sstate := set_regs_pc gv_e3 [] (0x91f98 + 4).
(* to __interceptor_vfprintf through __wrap_vfprintf *)
Definition gv_e4 : sstate := Eval vm_compute in fst (GVTO A_VFPI gv_s3).
Lemma r_gv4 : GVTO A_VFPI gv_s3 = (gv_e4, RS_running). Proof. vm_compute. reflexivity. Qed.
Definition gv_e4r : YP09.region := Eval vm_compute in hd gv_stk0 (ss_mem gv_e4).
Lemma gv_e4_mem : ss_mem gv_e4 = gv_e4r :: [gv_can]. Proof. vm_compute. reflexivity. Qed.
(* after the call: havoc from atom 49; the canary copy and the saved registers stay *)
Definition gv_s5 : sstate := kafter 49 gv_e4 RA_VFPI (-304) (-304) (-56).
Definition gv_e5 : sstate := Eval vm_compute in fst (GVRUN gv_s5).
Lemma r_gv5 : GVRUN gv_s5 = (gv_e5, RS_stopped (SR_jalr (SOff 1 0))). Proof. vm_compute. reflexivity. Qed.

(* ---- the shape checks ---- *)
Definition gv_wb (r : YP09.region) : bool :=
  match YP09.r_base r with Some 2%nat => (- gvK <=? YP09.r_wlo r) && (YP09.r_whi r <=? 0) | _ => false end
  || (YP09.r_whi r <=? YP09.r_wlo r).
Definition gv_win (rs : smem) : bool := forallb gv_wb rs.
Definition gv_stk (rs : smem) : bool :=
  match rs with
  | r :: _ => obase_eqb (YP09.r_base r) (Some 2%nat) && (YP09.r_wlo r =? - gvK) && (YP09.r_whi r =? 0)
  | [] => false end.
Lemma c_w0 : gv_win (ss_mem gv_s0) = true. Proof. vm_compute. reflexivity. Qed.
Lemma c_k1 : gv_stk (ss_mem gv_e1) = true. Proof. vm_compute. reflexivity. Qed.
Lemma c_w2 : gv_win (ss_mem gv_s2) = true. Proof. vm_compute. reflexivity. Qed.
Lemma c_k3 : gv_stk (ss_mem gv_e3) = true. Proof. vm_compute. reflexivity. Qed.
Lemma c_w3 : gv_win (ss_mem gv_s3) = true. Proof. vm_compute. reflexivity. Qed.
Lemma c_k4 : gv_stk (ss_mem gv_e4) = true. Proof. vm_compute. reflexivity. Qed.
Lemma c_w5 : gv_win (ss_mem gv_s5) = true. Proof. vm_compute. reflexivity. Qed.
Lemma c_k5 : gv_stk (ss_mem gv_e5) = true. Proof. vm_compute. reflexivity. Qed.
(* at the memset call *)
Lemma c1_resv : ss_resv gv_e1d = None. Proof. vm_compute. reflexivity. Qed.
Lemma c1_pc : ss_pc gv_e1d = W_MEMSET. Proof. vm_compute. reflexivity. Qed.
Lemma c1_base : YP09.r_base gv_e1r = Some 2%nat. Proof. vm_compute. reflexivity. Qed.
Lemma c1_lo : YP09.r_lo gv_e1r = - gvK. Proof. vm_compute. reflexivity. Qed.
Lemma c1_hi : YP09.r_hi gv_e1r = 0. Proof. vm_compute. reflexivity. Qed.
Lemma c1_wlo : YP09.r_wlo gv_e1r = - gvK. Proof. vm_compute. reflexivity. Qed.
Lemma c1_whi : YP09.r_whi gv_e1r = 0. Proof. vm_compute. reflexivity. Qed.
Lemma c1_ra : sr_get (ss_regs gv_e1d) 1 = SLit RA_MSET. Proof. vm_compute. reflexivity. Qed.
Lemma c1_sp : sr_get (ss_regs gv_e1d) 2 = SOff 2 (-304). Proof. vm_compute. reflexivity. Qed.
Lemma c1_gp : sr_get (ss_regs gv_e1d) 3 = SOff 3 0. Proof. vm_compute. reflexivity. Qed.
Lemma c1_tp : sr_get (ss_regs gv_e1d) 4 = SOff 4 0. Proof. vm_compute. reflexivity. Qed.
Lemma c1_a0 : sr_get (ss_regs gv_e1d) 10 = SOff 2 (-304). Proof. vm_compute. reflexivity. Qed.
Lemma c1_a1 : sr_get (ss_regs gv_e1d) 11 = SLit 0. Proof. vm_compute. reflexivity. Qed.
Lemma c1_a2 : sr_get (ss_regs gv_e1d) 12 = SLit 232. Proof. vm_compute. reflexivity. Qed.
Lemma c1_at : ss_atoms_lt 33 gv_e1d = true. Proof. vm_compute. reflexivity. Qed.
Lemma c1_wf : regions_wf (ss_mem gv_k1) = true. Proof. vm_compute. reflexivity. Qed.
Lemma c1_nc : no_cdata (ss_mem gv_k1) = true. Proof. vm_compute. reflexivity. Qed.
Lemma c1_ma : mem_atoms_lt 33 (ss_mem gv_k1) = true. Proof. vm_compute. reflexivity. Qed.
Lemma c1_ci : forallb (chunk_inside gv_e1r) (YP09.r_chunks gv_e1r) = true. Proof. vm_compute. reflexivity. Qed.
Lemma c1_zc : chunk_inside gv_k1r gv_zc = true. Proof. vm_compute. reflexivity. Qed.
Lemma c1_kb : YP09.r_base gv_k1r = Some 2%nat. Proof. vm_compute. reflexivity. Qed.
(* at the D store *)
Lemma c3_pc : ss_pc gv_e3 = 0x91f98. Proof. vm_compute. reflexivity. Qed.
Lemma c3_resv : ss_resv gv_e3 = None. Proof. vm_compute. reflexivity. Qed.
Lemma c3_s3 : sr_get (ss_regs gv_e3) 19 = SOff 10 0. Proof. vm_compute. reflexivity. Qed.
Lemma c3_base : YP09.r_base gv_e3r = Some 2%nat. Proof. vm_compute. reflexivity. Qed.
Lemma c3_lo : YP09.r_lo gv_e3r = - gvK. Proof. vm_compute. reflexivity. Qed.
Lemma c3_hi : YP09.r_hi gv_e3r = 0. Proof. vm_compute. reflexivity. Qed.
Lemma c3_lk : clookup tbl_g 0x91f98 = Some 622627. Proof. vm_compute. reflexivity. Qed.
Lemma c3_ec : is_ecall (Z_to_bv 32 622627) = false. Proof. vm_compute. reflexivity. Qed.
Lemma c3_dec : decode_any (Z_to_bv 32 622627) = Some (Store SZ1 19%bv 0%bv 0%bv, 4%Z). Proof. vm_refl_bv. Qed.
(* at the __wrap_vfprintf call *)
Lemma c4_resv : ss_resv gv_e4 = None. Proof. vm_compute. reflexivity. Qed.
Lemma c4_pc : ss_pc gv_e4 = A_VFPI. Proof. vm_compute. reflexivity. Qed.
Lemma c4_base : YP09.r_base gv_e4r = Some 2%nat. Proof. vm_compute. reflexivity. Qed.
Lemma c4_lo : YP09.r_lo gv_e4r = - gvK. Proof. vm_compute. reflexivity. Qed.
Lemma c4_hi : YP09.r_hi gv_e4r = 0. Proof. vm_compute. reflexivity. Qed.
Lemma c4_wlo : YP09.r_wlo gv_e4r = - gvK. Proof. vm_compute. reflexivity. Qed.
Lemma c4_whi : YP09.r_whi gv_e4r = 0. Proof. vm_compute. reflexivity. Qed.
Lemma c4_ra : sr_get (ss_regs gv_e4) 1 = SLit RA_VFPI. Proof. vm_compute. reflexivity. Qed.
Lemma c4_sp : sr_get (ss_regs gv_e4) 2 = SOff 2 (-304). Proof. vm_compute. reflexivity. Qed.
Lemma c4_gp : sr_get (ss_regs gv_e4) 3 = SOff 3 0. Proof. vm_compute. reflexivity. Qed.
Lemma c4_tp : sr_get (ss_regs gv_e4) 4 = SOff 4 0. Proof. vm_compute. reflexivity. Qed.
Lemma c4_a0 : sr_get (ss_regs gv_e4) 10 = SOff 2 (-304). Proof. vm_compute. reflexivity. Qed.
Lemma c4_a1 : sr_get (ss_regs gv_e4) 11 = SOff 12 0. Proof. vm_compute. reflexivity. Qed.
Lemma c4_a2 : sr_get (ss_regs gv_e4) 12 = SOff 13 0. Proof. vm_compute. reflexivity. Qed.
Lemma c4_at : ss_atoms_lt 49 gv_e4 = true. Proof. vm_compute. reflexivity. Qed.
Lemma c4_wf : regions_wf (ss_mem gv_s5) = true. Proof. vm_compute. reflexivity. Qed.
Lemma c4_nc : no_cdata (ss_mem gv_s5) = true. Proof. vm_compute. reflexivity. Qed.
Lemma c4_ma : mem_atoms_lt 49 (ss_mem gv_s5) = true. Proof. vm_compute. reflexivity. Qed.
Lemma c4_ci : forallb (chunk_inside gv_e4r) (YP09.r_chunks gv_e4r) = true. Proof. vm_compute. reflexivity. Qed.
(* at the ret *)
Lemma c5_resv : ss_resv gv_e5 = None. Proof. vm_compute. reflexivity. Qed.
Lemma c5_ret : clookup tbl_g (ss_pc gv_e5) = Some RET_WORD_r. Proof. vm_compute. reflexivity. Qed.
Lemma c5_saved : forallb (fun i => sv_eqb (sr_get (ss_regs gv_e5) (Z_to_bv 5 i)) (SOff (Z.to_nat i) 0))
  [1; 2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27] = true.
Proof. vm_compute. reflexivity. Qed.
Lemma c5_a0 : sr_get (ss_regs gv_e5) 10 = sr_get (ss_regs gv_s5) 10. Proof. vm_compute. reflexivity. Qed.
End r.

(* ---- reading a FILE field off the chunks: a CZero chunk covering it, or a CVal chunk at it ---- *)
Definition gv_zchk (cs : list YP09.chunk) (off n : Z) : bool :=
  match find_chunk cs off n with
  | Some c => match YP09.c_val c with CZero _ => true | _ => false end
  | None => false end.
Definition gv_vget (cs : list YP09.chunk) (off n : Z) : option sv :=
  match find_chunk cs off n with
  | Some c => if YP09.c_off c =? off then
      match YP09.c_val c with CVal w e => if Z.of_N w =? n then Some e else None | _ => None end else None
  | None => None end.

Section v. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis TB : TfibSyms B.
Hypothesis AMEMSET : aintrin_realizesU B OSet W_MEMSET.
Hypothesis AVFPI : avfpi_realizes B A_VFPI.

Lemma gv_win_sound : forall E rs a, gv_win rs = true -> in_wrange E rs a ->
  base_val E (Some 2%nat) - gvK <= a < base_val E (Some 2%nat).
Proof.
intros E rs a Hok (r & Hin & Ha). unfold gv_win in Hok. rewrite forallb_forall in Hok.
specialize (Hok r Hin). unfold gv_wb in Hok. revert Ha Hok.
destruct (YP09.r_base r) as [[|[|[|n]]]|]; intros Ha Hok; cbn [orb] in Hok;
  try (apply Z.leb_le in Hok; lia).
apply orb_prop in Hok as [Hb|Hb].
- apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. lia.
- apply Z.leb_le in Hb. lia.
Qed.
Lemma gv_stk_sound : forall rs, gv_stk rs = true -> exists r rest, rs = r :: rest /\
  YP09.r_base r = Some 2%nat /\ YP09.r_wlo r = - gvK /\ YP09.r_whi r = 0.
Proof.
intros [|r rest] H; [discriminate|]. unfold gv_stk in H.
apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
exists r, rest. split; [reflexivity|]. split; [exact (obase_eqb_eq _ _ H1)|].
split; [exact (proj1 (Z.eqb_eq _ _) H2) | exact (proj1 (Z.eqb_eq _ _) H3)].
Qed.
Lemma gv_bv64_inj : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> Z_to_bv 64 x = Z_to_bv 64 y -> x = y.
Proof.
intros x y Hx Hy E. apply (f_equal bv_unsigned) in E. rewrite !unsigned_lit_small in E by lia. exact E.
Qed.
Lemma gv_fld_zero : forall E m base cs off (n : nat),
  Forall (YP09.chunk_ok tfibsegs E m base) cs -> gv_zchk cs off (Z.of_nat n) = true ->
  val_mem tfibsegs m (base + off) n 0.
Proof.
intros E m base cs off n Hcs Hz. unfold gv_zchk in Hz.
destruct (find_chunk cs off (Z.of_nat n)) as [c|] eqn:Ef; [|discriminate].
destruct c as [co cv]. cbn [YP09.c_val] in Hz. destruct cv as [w e| len | len | d s len]; try discriminate.
apply find_chunk_sound in Ef as (Hin & Hlo & Hhi). cbn [YP09.c_off YP09.c_len cv_len YP09.c_val] in Hlo, Hhi.
pose proof (proj1 (Forall_forall _ _) Hcs _ Hin) as Hck.
intros k Hk. destruct (Hck (off - co + Z.of_nat k) ltac:(cbn [YP09.c_len cv_len YP09.c_val]; lia)) as (b & Hb1 & Hb2).
cbn [cbyte YP09.c_val YP09.c_off] in Hb1, Hb2. injection Hb1 as <-.
replace (base + off + Z.of_nat k) with (base + co + (off - co + Z.of_nat k)) by lia. rewrite Hb2.
f_equal. unfold YO0f.le_byte. rewrite Zmod_0_l, Z.shiftr_0_l. reflexivity.
Qed.
Lemma gv_fld_val : forall E m base cs off (n : nat) e v,
  Forall (YP09.chunk_ok tfibsegs E m base) cs -> gv_vget cs off (Z.of_nat n) = Some e -> (n <= 8)%nat ->
  bv_unsigned (sv_denot E e) mod 2 ^ (8 * Z.of_nat n) = v ->
  val_mem tfibsegs m (base + off) n v.
Proof.
intros E m base cs off n e v Hcs Hv Hn8 Hval. unfold gv_vget in Hv.
destruct (find_chunk cs off (Z.of_nat n)) as [c|] eqn:Ef; [|discriminate].
destruct c as [co cv]. cbn [YP09.c_off YP09.c_val] in Hv.
destruct (co =? off) eqn:Ho; [|discriminate]. apply Z.eqb_eq in Ho. subst co.
destruct cv as [w e'| | |]; try discriminate.
destruct (Z.of_N w =? Z.of_nat n) eqn:Hw; [|discriminate]. apply Z.eqb_eq in Hw. injection Hv as <-.
apply find_chunk_sound in Ef as (Hin & _ & _).
pose proof (proj1 (Forall_forall _ _) Hcs _ Hin) as Hck.
intros k Hk. destruct (Hck (Z.of_nat k) ltac:(cbn [YP09.c_len cv_len YP09.c_val]; lia)) as (b & Hb1 & Hb2).
cbn [cbyte YP09.c_val YP09.c_off] in Hb1, Hb2. injection Hb1 as <-. rewrite Hb2. f_equal.
unfold YP09.byte_of_word, YO0f.le_byte. subst v.
apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with (2 ^ 8).
change 256 with (2 ^ 8). rewrite (Z.mod_mod _ (2 ^ (8 * Z.of_nat n))) by (apply Z.pow_nonzero; lia).
rewrite (Z.mod_mod _ (2 ^ 8)) by lia.
apply Z.bits_inj'. intros i Hi. destruct (Z_lt_le_dec i 8) as [Li|Li].
- rewrite !Z.mod_pow2_bits_low by lia. rewrite !Z.shiftr_spec by lia. rewrite Z.mod_pow2_bits_low by lia. reflexivity.
- rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

(* ---- adding a chunk to the first region ---- *)
Lemma gv_region_wf_add : forall r c, region_wf r = true -> chunk_inside r c = true -> region_wf (gv_addc r c) = true.
Proof.
intros [b lo hi wlo whi cs] c Hw Hc. unfold gv_addc, region_wf in *.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks] in *.
apply andb_true_iff in Hw as [Hw1 Hw2]. apply andb_true_iff. split; [exact Hw1|].
cbn [forallb]. apply andb_true_iff. split; [exact Hc | exact Hw2].
Qed.
Lemma gv_all_disjoint_add : forall E r c rs, all_disjoint E r rs -> all_disjoint E (gv_addc r c) rs.
Proof.
intros E r c rs. induction rs as [|x rs IH]; cbn [all_disjoint]; [tauto|].
intros [Hx Hr]. split; [exact Hx | exact (IH Hr)].
Qed.
Lemma gv_st_ok_add : forall E ss ms r rest c,
  st_ok tfibsegs E ss ms -> ss_mem ss = r :: rest -> chunk_inside r c = true ->
  YP09.chunk_ok tfibsegs E (ms_mem ms) (base_val E (YP09.r_base r)) c ->
  st_ok tfibsegs E (set_mem ss (gv_addc r c :: rest)) ms.
Proof.
intros E ss ms r rest c (H1 & H2 & H3 & H4 & H5 & H6 & H7 & (Hwf & Hok & Hpd) & H9) Hm Hci Hck.
rewrite Hm in Hwf, Hok, Hpd. unfold st_ok, set_mem. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts].
repeat (split; [assumption|]). split; [|exact H9]. split; [|split].
- cbn [regions_wf] in *. apply andb_true_iff in Hwf as [Hr Hrs]. apply andb_true_iff.
  split; [exact (gv_region_wf_add r c Hr Hci) | exact Hrs].
- apply Forall_cons; [|exact (Forall_inv_tail Hok)].
  pose proof (Forall_inv Hok) as (R1 & R2 & R3 & R4).
  split; [exact R1|]. split; [exact R2|]. split; [exact R3|]. apply Forall_cons; [exact Hck | exact R4].
- cbn [pairwise_disjoint] in *. destruct Hpd as [Ha Hb]. split; [exact (gv_all_disjoint_add E r c rest Ha) | exact Hb].
Qed.

Section w.
Variables (ly : alayout) (S : astate) (U : list (Z * Z)) (W : world tfibsegs) (regs : bvmap 5 word)
  (mem : word -> option byte) (md : Model) (sp0 D N M f : Z) (ps : list fpiece) (P : Z) (args out : list Z) (cval : Z).
Hypothesis HPRE : gl_pre B ly S U W mem md sp0 D N M f ps P args out.
Hypothesis HREGS : snk_regs B regs (sp0 + OSP_VSN).
Hypothesis G10 : getr regs 10 = w64 D.
Hypothesis G11 : getr regs 11 = w64 N.
Hypothesis G12 : getr regs 12 = w64 f.
Hypothesis G13 : getr regs 13 = w64 P.
Hypothesis HCAN : val_mem tfibsegs (mrestrict (w_H W) mem) FM_canary 8 cval.
Hypothesis HCV : 0 <= cval < 2 ^ 64.

Lemma gv_num : alloc_ceiling <= ly_stk_lo ly /\ 2 ^ 44 <= sp0 /\ sp0 mod 16 = 0 /\ ly_stk_lo ly + SNK_STK <= sp0 /\
  sp0 + 0x200 <= ly_stk_hi ly /\ sp0 + 0x200 <= 2 ^ 47 /\ kHighMemBeg <= sp0 - SNK_STK /\ 0 < D /\
  D + M <= alloc_ceiling /\ 1 <= M /\ (D + M <= FM_canary \/ FM_canary + 8 <= D) /\
  Z.of_nat (length out) + 1 <= M <= N /\ N <= 2 ^ 30 /\ sp0 + 0x200 <= P.
Proof.
destruct HPRE as ((_ & H1 & H2 & H3 & H4 & H5 & H6 & H7 & _) & _ & _ & _ & _ & HP1 & _ & _ & _ & HM & HN &
  (D1 & D2 & D3 & D4 & _)).
repeat split; try assumption; lia.
Qed.
Lemma gv_base : snk_base B ly S U W mem md sp0.
Proof. exact (proj1 HPRE). Qed.
Lemma gv_dest : snk_dest B ly S W mem D M.
Proof. destruct HPRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & X). exact X. Qed.
Ltac gvn := pose proof gv_num as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & N10 & N11 & N12 & N13 & N14);
  pose proof ac_bounds as ACB; assert (HSS : SNK_STK = 9104) by reflexivity.

Definition gvE0 : env := Ereg regs [Z_to_bv 64 cval].
Definition gvOK (E : env) : Prop := forall i, (i < 33)%nat -> ew E i = ew gvE0 i.
Definition gvFR (XW : Z -> Prop) (m : word -> option byte) (mdX : Model) : Prop :=
  snk_frame B ly S U W mem md sp0 (sp0 + OSP_VSN) XW m mdX.
Definition gvQ : world tfibsegs -> config -> Prop :=
  gl_post B ly S U W regs mem md sp0 (sp0 + OSP_VSN) (dst_xw D M) D out.

Lemma gvOK_E0 : gvOK gvE0.
Proof. intros i _. reflexivity. Qed.
Lemma gvOK_havoc : forall E k ws, gvOK E -> (33 <= k)%nat -> gvOK (havoc E k ws).
Proof. intros E k ws HE Hk i Hi. rewrite ew_havoc_old by lia. exact (HE i Hi). Qed.
Lemma gvOK_reg : forall E i (r : bv 5), gvOK E -> Z.of_nat i = bv_unsigned r -> ew E i = getr regs r.
Proof.
intros E i r HE Hi. pose proof (u5_range r) as Hr.
rewrite (HE i) by lia. unfold gvE0. exact (ew_Ereg_nat regs _ i r Hi).
Qed.
Lemma gvOK_sp : forall E, gvOK E -> bv_unsigned (ew E 2) = sp0 + OSP_VSN.
Proof.
intros E HE. gvn. rewrite (gvOK_reg E 2 2%bv HE eq_refl). destruct HREGS as (_ & R2 & _). rewrite R2.
unfold w64. apply unsigned_lit_small. unfold OSP_VSN. lia.
Qed.
Lemma gvOK_can : forall E, gvOK E -> ew E 32 = Z_to_bv 64 cval.
Proof. intros E HE. rewrite (HE 32%nat) by lia. unfold gvE0. exact (ew_Ereg_extra regs _ 0). Qed.
Lemma gv_den_reg : forall E i (r : bv 5), gvOK E -> Z.of_nat i = bv_unsigned r -> sv_denot E (SOff i 0) = getr regs r.
Proof. intros E i r HE Hi. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact (gvOK_reg E i r HE Hi). Qed.
Lemma gv_den_sp : forall E z, gvOK E -> sv_denot E (SOff 2 z) = Z_to_bv 64 (sp0 + OSP_VSN + z).
Proof. intros E z HE. cbn [sv_denot]. rewrite (gvOK_sp E HE). reflexivity. Qed.
Lemma gv_rd : forall E ss ms (r : bv 5), st_ok tfibsegs E ss (restrict (w_H W) ms) ->
  getr (ms_regs ms) r = sv_denot E (sr_get (ss_regs ss) r).
Proof. intros E ss ms r HS. exact (st_ok_reg_denot (w_H W) E ss ms r HS). Qed.

(* ---- the frame: FMsnprintfI's snk_frame below sp0 + 0x160 ---- *)
Lemma gv_frame_init : gvFR (fun a => a = D) mem md.
Proof. gvn. apply (g_frame_init B ly S U W mem md sp0 (sp0 + OSP_VSN) _ gv_base). unfold OSP_VSN. lia. Qed.
Lemma gv_frame_weak : forall (XW XW' : Z -> Prop) m mdX, (forall a, XW a -> XW' a) -> gvFR XW m mdX -> gvFR XW' m mdX.
Proof.
intros XW XW' m mdX Hx (HA & Hs & Hp & Hf & Hpm). split; [exact HA|]. split; [exact Hs|]. split; [exact Hp|].
split; [|exact Hpm]. intros a Ha H1 H2. apply Hf; [exact Ha | exact H1 | intros X; apply H2; apply Hx; exact X].
Qed.
(* a run of the walk's own code: its windows lie in the stack region, below sp0 + 0x160 *)
Lemma gv_frame_run : forall XW E ss ss' ms ms1 mdX mat1,
  gvFR XW (ms_mem ms) mdX -> gvOK E -> st_ok tfibsegs E ss' (restrict (w_H W) ms1) ->
  frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms1) -> gv_win (ss_mem ss) = true -> gv_stk (ss_mem ss') = true ->
  gvFR XW (ms_mem ms1) (with_vm_backing (m_vm_lazy mdX) mat1 mdX).
Proof.
intros XW E ss ss' ms ms1 mdX mat1 HF HE HS1 Hfo Hw Hk.
pose proof (gvOK_sp E HE) as E2. gvn.
apply (g_frame_run B LAWS ly S U W mem md sp0 (sp0 + OSP_VSN) XW gv_base (ms_mem ms) mdX (ms_mem ms1) mat1 E
  (ss_mem ss) HF).
- intros a Ha. pose proof (gv_win_sound E _ a Hw Ha) as X. cbn [base_val] in X. rewrite E2 in X.
  unfold snk_band, gvK, OSP_VSN in *. lia.
- exact Hfo.
- intros a Hb. destruct (gv_stk_sound _ Hk) as (r & rest & Hrs & Hb2 & Hlo & Hhi).
  destruct (Z_lt_le_dec a (sp0 + OSP_VSN)) as [L|L].
  + apply (st_ok_window_apresent (w_H W) E ss' ms1 0 r a HS1); [rewrite Hrs; reflexivity | |].
    * rewrite Hb2, Hlo, Hhi. cbn [base_val]. rewrite E2. unfold snk_band, gvK, OSP_VSN in *. lia.
    * unfold snk_band, TFIB_IMG_END in *. lia.
  + destruct HF as (_ & _ & Hp & _). destruct (Hp a Hb) as [Hh [bb Hbb]]. split; [exact Hh|]. exists bb.
    rewrite (Hfo (Z_to_bv 64 a)); [exact Hbb|]. rewrite unsigned_lit_small by (unfold snk_band in Hb; lia).
    intros Hin. pose proof (gv_win_sound E _ a Hw Hin) as X. cbn [base_val] in X. rewrite E2 in X. lia.
Qed.
(* the bytes below the band do not change in a run *)
Lemma gv_run_low : forall E ss (m m' : word -> option byte) a, gvOK E -> frame_of E (ss_mem ss) m m' ->
  gv_win (ss_mem ss) = true -> 0 <= a < sp0 - SNK_STK -> aview tfibsegs (w_H W) m' a = aview tfibsegs (w_H W) m a.
Proof.
intros E ss m m' a HE Hfo Hw Ha. gvn. apply aview_same. apply Hfo. rewrite unsigned_lit_small by lia.
intros Hin. pose proof (gv_win_sound E _ a Hw Hin) as X. cbn [base_val] in X. rewrite (gvOK_sp E HE) in X.
unfold gvK, OSP_VSN in X. lia.
Qed.
(* the step `sb zero, 0(s3)` at D *)
Lemma gv_store_frame : forall m m' mdX mat,
  gvFR (fun a => a = D) m mdX -> writable_at tfibsegs (mrestrict (w_H W) m) D ->
  (forall x : word, m' x = if bv_eqb x (Z_to_bv 64 D) then Some (Z_to_bv 8 0) else m x) ->
  gvFR (fun a => a = D) m' (with_vm_backing (m_vm_lazy mdX) mat mdX) /\ aview tfibsegs (w_H W) m' D = Some 0.
Proof.
intros m m' mdX mat HF Hwr Hm. gvn.
pose proof gv_dest as (D1 & D2 & D3 & D4 & D5 & _).
assert (HDr : 0 <= D < 2 ^ 64) by lia.
pose proof (writable_unhidden W m D HDr Hwr) as Hh.
assert (Hsame : forall x : word, bv_eqb x (Z_to_bv 64 D) = false -> m' x = m x).
{ intros x Hx. rewrite Hm, Hx. reflexivity. }
assert (Hne : forall a, 0 <= a < 2 ^ 64 -> a <> D -> bv_eqb (Z_to_bv 64 a) (Z_to_bv 64 D) = false).
{ intros a Ha Hn. destruct (bv_eqb (Z_to_bv 64 a) (Z_to_bv 64 D)) eqn:Eq; [|reflexivity].
  exfalso. apply bv_eqb_eq in Eq. exact (Hn (gv_bv64_inj a D Ha HDr Eq)). }
assert (HmD : m' (Z_to_bv 64 D) = Some (Z_to_bv 8 0)).
{ rewrite Hm. rewrite (proj2 (bv_eqb_eq (Z_to_bv 64 D) (Z_to_bv 64 D)) eq_refl). reflexivity. }
assert (Hpres : forall a, apresent (w_H W) m a -> apresent (w_H W) m' a).
{ intros a [Hha [b Hb]]. split; [exact Hha|]. rewrite Hm.
  destruct (bv_eqb (Z_to_bv 64 a) (Z_to_bv 64 D)); [eexists; reflexivity | exists b; exact Hb]. }
pose proof (same_but_materialized_frame mdX _ (with_vm_backing_same mdX mat)) as MF.
split.
- apply (g_frame_step B ly S U W mem md sp0 (sp0 + OSP_VSN) _ m mdX m' _ HF).
  + destruct HF as (HA & _). apply (ARU_frame tfibsegs B LAWS ly S U W m mdX m' _ HA).
    * intros a Ha Hown. apply aview_same. apply Hsame. apply Hne; [exact Ha|]. intros ->.
      destruct (D5 D ltac:(lia)) as (_ & X & _). exact (X Hown).
    * intros a Hv. destruct (bv_eqb (Z_to_bv 64 a) (Z_to_bv 64 D)) eqn:Eq.
      -- apply bv_eqb_eq in Eq. unfold aview, mbyte, mrestrict. rewrite Eq, Hh, HmD. discriminate.
      -- rewrite (aview_same (w_H W) m m' a (Hsame _ Eq)). exact Hv.
    * apply MF. * apply MF. * apply MF.
    * intros a _ Hha. apply Hsame. destruct (bv_eqb (w64 a) (Z_to_bv 64 D)) eqn:Eq; [|reflexivity].
      apply bv_eqb_eq in Eq. rewrite Eq, Hh in Hha. discriminate.
  + apply with_vm_backing_same.
  + intros a Ha. apply Hpres. destruct HF as (_ & _ & Hp & _). exact (Hp a Ha).
  + intros a Ha _ Hx. apply aview_same. apply Hsame. exact (Hne a Ha Hx).
  + exact Hpres.
- unfold aview, mbyte, mrestrict. rewrite Hh, HmD. reflexivity.
Qed.

(* ---- the FILE fields at the call: the chunks of the stack region at gv_e4 ---- *)
Lemma gv_fz4 : forall E m o (n : nat),
  Forall (YP09.chunk_ok tfibsegs E (mrestrict (w_H W) m) (sp0 + OSP_VSN)) (YP09.r_chunks gv_e4r) ->
  gv_zchk (YP09.r_chunks gv_e4r) (-304 + o) (Z.of_nat n) = true ->
  val_mem tfibsegs (mrestrict (w_H W) m) (sp0 + FO + o) n 0.
Proof.
intros E m o n Hcs Hz. replace (sp0 + FO + o) with (sp0 + OSP_VSN + (-304 + o)) by (unfold FO, OSP_VSN; lia).
exact (gv_fld_zero E _ _ _ _ n Hcs Hz).
Qed.
Lemma gv_fv4 : forall E m o (n : nat) e v,
  Forall (YP09.chunk_ok tfibsegs E (mrestrict (w_H W) m) (sp0 + OSP_VSN)) (YP09.r_chunks gv_e4r) ->
  gv_vget (YP09.r_chunks gv_e4r) (-304 + o) (Z.of_nat n) = Some e -> (n <= 8)%nat ->
  bv_unsigned (sv_denot E e) mod 2 ^ (8 * Z.of_nat n) = v ->
  val_mem tfibsegs (mrestrict (w_H W) m) (sp0 + FO + o) n v.
Proof.
intros E m o n e v Hcs Hv Hn Hval. replace (sp0 + FO + o) with (sp0 + OSP_VSN + (-304 + o)) by (unfold FO, OSP_VSN; lia).
exact (gv_fld_val E _ _ _ _ n e v Hcs Hv Hn Hval).
Qed.

(* ---- the epilogue: canary check, restore, ret ---- *)
Lemma gv_epi : forall E ms mdX, gvOK E -> st_ok tfibsegs E gv_s5 (restrict (w_H W) ms) ->
  gvFR (dst_xw D M) (ms_mem ms) mdX -> getr (ms_regs ms) 10 = w64 (Z.of_nat (length out)) ->
  (forall i, 0 <= i <= Z.of_nat (length out) ->
     aview tfibsegs (w_H W) (ms_mem ms) (D + i) = Some (nth (Z.to_nat i) (out ++ [0]) 0)) ->
  SRr tfibsegs W (mkCfg ms mdX) gvQ.
Proof.
intros E ms mdX HE HS HF Ha0 Hout. gvn.
eapply SRr_bind; [exact (g_phase W E gv_s5 gv_e5 _ ms mdX HS r_gv5)|].
intros W' c' _ (-> & ms6 & mat6 & -> & HS6 & HF6).
pose proof (gv_frame_run _ E gv_s5 gv_e5 ms ms6 mdX mat6 HF HE HS6 HF6 c_w5 c_k5) as HF6'.
apply (g_ret W E gv_e5 ms6 _ gvQ HS6 c5_resv c5_ret).
intros mat'.
assert (RK : forall (r : bv 5) i, Z.of_nat i = bv_unsigned r ->
  In (Z.of_nat i) [1; 2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27] -> getr (ms_regs ms6) r = getr regs r).
{ intros r i Hi Hin. pose proof c5_saved as C. rewrite forallb_forall in C. specialize (C _ Hin). cbv beta in C.
  rewrite Nat2Z.id in C. apply sv_eqb_eq in C. rewrite Hi, Z_to_bv_bv_unsigned in C.
  rewrite (gv_rd E gv_e5 ms6 r HS6), C. exact (gv_den_reg E i r HE Hi). }
assert (P1 : getr (ms_regs ms6) 1 = getr regs 1) by exact (RK 1%bv 1%nat eq_refl ltac:(cbn; tauto)).
destruct HREGS as (Hret & _). unfold YK0s.ret_ok in Hret.
unfold gvQ, gl_post. split; [reflexivity|].
exists (ms_regs ms6), (ms_mem ms6), (with_vm_backing (m_vm_lazy (with_vm_backing (m_vm_lazy mdX) mat6 mdX)) mat'
  (with_vm_backing (m_vm_lazy mdX) mat6 mdX)).
split; [unfold cfg_at, raZ, w64; rewrite P1, Z_to_bv_bv_unsigned, Hret; reflexivity|].
split.
{ apply (g_frame_run B LAWS ly S U W mem md sp0 (sp0 + OSP_VSN) (dst_xw D M) gv_base (ms_mem ms6) _ (ms_mem ms6)
    mat' E [] HF6').
  - intros a (r & [] & _).
  - apply frame_of_refl.
  - destruct HF6' as (_ & _ & Hp & _). exact Hp. }
split.
{ intros r Hr. assert (Hr' : 0 <= r < 32) by (unfold acallee_saved in Hr; lia).
  apply (RK (Z_to_bv 5 r) (Z.to_nat r)).
  - rewrite Z2Nat.id by lia. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with (2 ^ 5).
    rewrite Z.mod_small by lia. reflexivity.
  - rewrite Z2Nat.id by lia. unfold acallee_saved in Hr. cbn [In]. lia. }
split.
{ rewrite (gv_rd E gv_e5 ms6 10 HS6), c5_a0, <- (gv_rd E gv_s5 ms 10 HS). exact Ha0. }
intros i Hi. rewrite <- (Hout i Hi). apply (gv_run_low E gv_s5 (ms_mem ms) (ms_mem ms6) (D + i) HE HF6 c_w5). lia.
Qed.

(* ---- the call of __wrap_vfprintf = __interceptor_vfprintf (sp0 + FO, f, P) ---- *)
Lemma gv_call2 : forall E ms mdX, gvOK E -> st_ok tfibsegs E gv_e4 (restrict (w_H W) ms) ->
  gvFR (fun a => a = D) (ms_mem ms) mdX -> aview tfibsegs (w_H W) (ms_mem ms) D = Some 0 ->
  SRr tfibsegs W (mkCfg ms mdX) gvQ.
Proof.
intros E ms mdX HE HS HF HD0. gvn. pose proof (gvOK_sp E HE) as E2.
assert (R1 : getr (ms_regs ms) 1 = Z_to_bv 64 RA_VFPI) by (rewrite (gv_rd E gv_e4 ms 1 HS), c4_ra; reflexivity).
assert (R2 : getr (ms_regs ms) 2 = w64 (sp0 + OSP_VFPI)).
{ rewrite (gv_rd E gv_e4 ms 2 HS), c4_sp, (gv_den_sp E _ HE). unfold w64, OSP_VFPI, OSP_VSN. f_equal. lia. }
assert (R3 : getr (ms_regs ms) 3 = w64 (as_gp B)).
{ rewrite (gv_rd E gv_e4 ms 3 HS), c4_gp, (gv_den_reg E 3 3%bv HE eq_refl). destruct HREGS as (_ & _ & X & _). exact X. }
assert (R4 : getr (ms_regs ms) 4 = w64 (as_tp B)).
{ rewrite (gv_rd E gv_e4 ms 4 HS), c4_tp, (gv_den_reg E 4 4%bv HE eq_refl). destruct HREGS as (_ & _ & _ & X). exact X. }
assert (R10 : getr (ms_regs ms) 10 = w64 (sp0 + FO)).
{ rewrite (gv_rd E gv_e4 ms 10 HS), c4_a0, (gv_den_sp E _ HE). unfold w64, FO, OSP_VSN. f_equal. lia. }
assert (R11 : getr (ms_regs ms) 11 = w64 f).
{ rewrite (gv_rd E gv_e4 ms 11 HS), c4_a1, (gv_den_reg E 12 12%bv HE eq_refl). exact G12. }
assert (R12 : getr (ms_regs ms) 12 = w64 P).
{ rewrite (gv_rd E gv_e4 ms 12 HS), c4_a2, (gv_den_reg E 13 13%bv HE eq_refl). exact G13. }
pose proof HF as (HA4 & Hsb4 & Hp4 & Hk4 & Hpm4).
(* gl_pre at the call *)
assert (HPRE4 : gl_pre B ly S U W (ms_mem ms) mdX sp0 D N M f ps P args out).
{ apply (gl_pre_xfer B LAWS TB ly S U W mem md (ms_mem ms) mdX sp0 D N M f ps P args out HPRE HA4 Hp4);
    [|right; exact HD0 | exact Hpm4].
  intros a Ha Hout Hne. apply Hk4; [exact Ha | intros C; apply Hout; unfold OSP_VSN in *; lia | exact Hne]. }
(* the FILE and the cookie *)
assert (HCS : Forall (YP09.chunk_ok tfibsegs E (mrestrict (w_H W) (ms_mem ms)) (sp0 + OSP_VSN)) (YP09.r_chunks gv_e4r)).
{ pose proof (st_ok_mem_ok tfibsegs E gv_e4 _ HS) as (_ & Hrs & _). rewrite gv_e4_mem in Hrs.
  apply Forall_inv in Hrs. destruct Hrs as (_ & _ & _ & Hcs). rewrite c4_base in Hcs. cbn [base_val] in Hcs.
  rewrite E2 in Hcs. exact Hcs. }
assert (HVF : vsn_file W (ms_mem ms) sp0 D N).
{ split; [|exact HD0]. unfold vsn_fields. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
  all: try (apply (gv_fz4 E (ms_mem ms)); [exact HCS | vm_compute; reflexivity]).
  - apply (gv_fv4 E (ms_mem ms) 72 8 (SLit 597976)); [exact HCS | vm_compute; reflexivity | lia | vm_compute; reflexivity].
  - apply (gv_fv4 E (ms_mem ms) 88 8 (SOff 2 (-49))); [exact HCS | vm_compute; reflexivity | lia |].
    rewrite (gv_den_sp E _ HE). rewrite unsigned_lit_small by (unfold OSP_VSN; lia). change (8 * Z.of_nat 8) with 64.
    rewrite Z.mod_small by (unfold OSP_VSN; lia). unfold FO, OSP_VSN. lia.
  - apply (gv_fv4 E (ms_mem ms) 140 4 (SLit 18446744073709551615)); [exact HCS | vm_compute; reflexivity | lia | vm_compute; reflexivity].
  - apply (gv_fv4 E (ms_mem ms) 144 4 (SLit 18446744073709551615)); [exact HCS | vm_compute; reflexivity | lia | vm_compute; reflexivity].
  - apply (gv_fv4 E (ms_mem ms) 152 8 (SOff 2 (-72))); [exact HCS | vm_compute; reflexivity | lia |].
    rewrite (gv_den_sp E _ HE). rewrite unsigned_lit_small by (unfold OSP_VSN; lia). change (8 * Z.of_nat 8) with 64.
    rewrite Z.mod_small by (unfold OSP_VSN; lia). unfold CKO, FO, OSP_VSN. lia.
  - apply (gv_fv4 E (ms_mem ms) 232 8 (SOff 10 0)); [exact HCS | vm_compute; reflexivity | lia |].
    rewrite (gv_den_reg E 10 10%bv HE eq_refl), G10. unfold w64. rewrite unsigned_lit_small by lia.
    change (8 * Z.of_nat 8) with 64. apply Z.mod_small. lia.
  - apply (gv_fv4 E (ms_mem ms) 240 8 (SOff 11 (-1))); [exact HCS | vm_compute; reflexivity | lia |].
    cbn [sv_denot]. rewrite (gvOK_reg E 11 11%bv HE eq_refl), G11. unfold w64.
    rewrite (unsigned_lit_small N) by lia. rewrite unsigned_lit_small by lia.
    change (8 * Z.of_nat 8) with 64. apply Z.mod_small. lia. }
assert (HR4 : snk_regs B (ms_regs ms) (sp0 + OSP_VFPI)).
{ split; [rewrite R1; apply ret_ok_lit; [unfold RA_VFPI; lia | reflexivity]|].
  split; [exact R2|]. split; [exact R3 | exact R4]. }
eapply SRr_bind.
{ apply (kcall W E gv_e4 ms mdX (sp0 + OSP_VSN) gvK gv_e4r [gv_can] 49 RA_VFPI (-304) (-304) (-56) (SNK_STK + 48)
    (vf_xw sp0 D M)
    (fun regs2 mem2 md2 => snk_frame B ly S U W (ms_mem ms) mdX sp0 (sp0 + OSP_VFPI) (vf_xw sp0 D M) mem2 md2 /\
       getr regs2 10 = w64 (Z.of_nat (length out)) /\
       (forall i, 0 <= i <= Z.of_nat (length out) ->
          aview tfibsegs (w_H W) mem2 (D + i) = Some (nth (Z.to_nat i) (out ++ [0]) 0)))
    HS c4_resv E2 gv_e4_mem c4_base c4_lo c4_hi ltac:(rewrite c4_wlo; lia) ltac:(rewrite c4_whi; lia)
    c4_ra c4_sp c4_at c4_wf c4_nc c4_ma c4_ci ltac:(lia) ltac:(unfold gvK; lia) ltac:(lia)
    ltac:(unfold gvK, OSP_VSN; lia) ltac:(unfold OSP_VSN; lia)).
  - intros a [Hf|Hd] Hs; unfold CKO, FO, OSP_VSN, gvK, dst_xw in *; lia.
  - intros r a [<-|[]] Ha. unfold gv_can in Ha. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val] in Ha.
    split; [unfold FM_canary in *; lia|]. split; [unfold FM_canary, OSP_VSN in *; lia|].
    intros [Hf|Hd]; unfold CKO, FO, dst_xw, FM_canary in *; lia.
  - intros r a [<-|[]] Ha. unfold gv_can in Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. lia.
  - intros a Ha. apply Hp4. unfold snk_band, gvK, OSP_VSN in *. lia.
  - rewrite c4_pc. eapply SRr_mono;
      [exact (AVFPI ly S U W (ms_regs ms) (ms_mem ms) mdX sp0 D N M f ps P args out HPRE4 HR4 R10 R11 R12 HVF)|].
    intros W' c' _ (-> & regs' & mem' & md' & -> & Hfr' & Hpr' & Ha0' & Hout').
    split; [reflexivity|]. exists regs', mem', md'.
    split; [unfold raZ; rewrite R1, unsigned_lit_small by (unfold RA_VFPI; lia); reflexivity|].
    split; [exact Hpr'|]. pose proof Hfr' as (HA' & Hsb' & Hp' & Hk' & Hpm').
    split; [exact Hsb'|]. split.
    { intros a Ha Hb Hx. apply Hk'; [exact Ha | | exact Hx]. intros C. apply Hb. unfold OSP_VFPI, OSP_VSN in *. lia. }
    split; [exact Hpm'|]. split; [exact Hfr'|]. split; [exact Ha0' | exact Hout']. }
intros W' c' _ (-> & ms5 & mat5 & -> & HS5 & HP5 & Hfr5 & Hpm5 & (HF5 & Ha05 & Hout5)).
apply (gv_epi (havoc E 49 (map (getr (ms_regs ms5)) CLOB)) ms5 _ (gvOK_havoc E 49 _ HE ltac:(lia)) HS5);
  [| exact Ha05 | exact Hout5].
pose proof HF5 as (HA5 & _ & Hp5 & _ & _).
apply (g_frame_step B ly S U W mem md sp0 (sp0 + OSP_VSN) _ (ms_mem ms) mdX (ms_mem ms5) _
  (gv_frame_weak (fun a => a = D) (dst_xw D M) _ _ ltac:(intros a ->; unfold dst_xw; lia) HF) HA5
  (with_vm_backing_same mdX mat5) Hp5).
- intros a Ha Hout Hx. apply Hfr5; [exact Ha | intros C; apply Hout; unfold OSP_VSN in *; lia |].
  intros [C|C]; [apply Hout; unfold CKO, FO, OSP_VSN in *; lia | exact (Hx C)].
- exact Hpm5.
Qed.

(* ---- from after the D store to the call ---- *)
Lemma gv_run3 : forall E ms mdX, gvOK E -> st_ok tfibsegs E gv_s3 (restrict (w_H W) ms) ->
  gvFR (fun a => a = D) (ms_mem ms) mdX -> aview tfibsegs (w_H W) (ms_mem ms) D = Some 0 ->
  SRr tfibsegs W (mkCfg ms mdX) gvQ.
Proof.
intros E ms mdX HE HS HF HD0. gvn.
eapply SRr_bind; [exact (g_phase_to W E A_VFPI gv_s3 gv_e4 _ ms mdX HS r_gv4)|].
intros W' c' _ (-> & ms4 & mat4 & -> & HS4 & HF4).
apply (gv_call2 E ms4 _ HE HS4 (gv_frame_run _ E gv_s3 gv_e4 ms ms4 mdX mat4 HF HE HS4 HF4 c_w3 c_k4)).
rewrite (gv_run_low E gv_s3 (ms_mem ms) (ms_mem ms4) D HE HF4 c_w3); [exact HD0 | lia].
Qed.

(* ---- `sb zero, 0(s3)`: *D = 0 ---- *)
Lemma gv_store : forall E ms mdX, gvOK E -> st_ok tfibsegs E gv_e3 (restrict (w_H W) ms) ->
  gvFR (fun a => a = D) (ms_mem ms) mdX -> SRr tfibsegs W (mkCfg ms mdX) gvQ.
Proof.
intros E ms mdX HE HS HF. gvn. pose proof (gvOK_sp E HE) as E2.
pose proof gv_dest as (D1 & D2 & D3 & D4 & D5 & _).
assert (HW : writable_at tfibsegs (mrestrict (w_H W) (ms_mem ms)) D).
{ destruct (D5 D ltac:(lia)) as (Hw & _ & _). destruct HF as (_ & _ & _ & _ & Hpm).
  exact (writable_xfer (w_H W) mem (ms_mem ms) D Hw (Hpm D)). }
assert (R19 : getr (ms_regs ms) 19 = Z_to_bv 64 D).
{ rewrite (gv_rd E gv_e3 ms 19 HS), c3_s3, (gv_den_reg E 10 10%bv HE eq_refl). exact G10. }
eapply SRr_bind.
{ apply (kstore0 tbl_g W E gv_e3 ms mdX 0x91f98 622627 19%bv D tbl_g_ok HS c3_pc c3_resv ltac:(lia) ltac:(lia)
    c3_lk c3_ec c3_dec R19 ltac:(lia) HW).
  intros r x Hr Hx Heq. rewrite gv_e3_mem in Hr. destruct Hr as [<-|[<-|[]]].
  - rewrite c3_base, c3_lo, c3_hi in Hx. cbn [base_val] in Hx. rewrite E2 in Hx.
    apply gv_bv64_inj in Heq; [| unfold gvK, OSP_VSN in *; lia | lia]. unfold gvK, OSP_VSN in *. lia.
  - unfold gv_can in Hx. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val] in Hx.
    apply gv_bv64_inj in Heq; [| unfold FM_canary in *; lia | lia]. unfold FM_canary in *. lia. }
intros W' c' _ (-> & ms1 & mat1 & -> & HS1 & HR1 & HM1).
destruct (gv_store_frame (ms_mem ms) (ms_mem ms1) mdX mat1 HF HW HM1) as [HF1 HD1].
exact (gv_run3 E ms1 _ HE HS1 HF1 HD1).
Qed.

(* ---- after memset: the FILE stores up to the D store ---- *)
Lemma gv_run2 : forall E ms mdX, gvOK E -> st_ok tfibsegs E gv_s2 (restrict (w_H W) ms) ->
  gvFR (fun a => a = D) (ms_mem ms) mdX -> SRr tfibsegs W (mkCfg ms mdX) gvQ.
Proof.
intros E ms mdX HE HS HF.
eapply SRr_bind; [exact (g_phase_to W E A_VFPI gv_s2 gv_e3 _ ms mdX HS r_gv3)|].
intros W' c' _ (-> & ms3 & mat3 & -> & HS3 & HF3).
exact (gv_store E ms3 _ HE HS3 (gv_frame_run _ E gv_s2 gv_e3 ms ms3 mdX mat3 HF HE HS3 HF3 c_w2 c_k3)).
Qed.

(* ---- the memset (sp, 0, 0xe8) call ---- *)
Lemma gv_call1 : forall E ms mdX, gvOK E -> st_ok tfibsegs E gv_e1d (restrict (w_H W) ms) ->
  gvFR (fun a => a = D) (ms_mem ms) mdX -> SRr tfibsegs W (mkCfg ms mdX) gvQ.
Proof.
intros E ms mdX HE HS HF. gvn. pose proof (gvOK_sp E HE) as E2.
pose proof HF as (HA1 & Hsb1 & Hp1 & Hk1 & Hpm1).
assert (R1 : getr (ms_regs ms) 1 = Z_to_bv 64 RA_MSET) by (rewrite (gv_rd E gv_e1d ms 1 HS), c1_ra; reflexivity).
assert (R2 : getr (ms_regs ms) 2 = w64 (sp0 + FO)).
{ rewrite (gv_rd E gv_e1d ms 2 HS), c1_sp, (gv_den_sp E _ HE). unfold w64, FO, OSP_VSN. f_equal. lia. }
assert (R3 : getr (ms_regs ms) 3 = w64 (as_gp B)).
{ rewrite (gv_rd E gv_e1d ms 3 HS), c1_gp, (gv_den_reg E 3 3%bv HE eq_refl). destruct HREGS as (_ & _ & X & _). exact X. }
assert (R4 : getr (ms_regs ms) 4 = w64 (as_tp B)).
{ rewrite (gv_rd E gv_e1d ms 4 HS), c1_tp, (gv_den_reg E 4 4%bv HE eq_refl). destruct HREGS as (_ & _ & _ & X). exact X. }
assert (R10 : getr (ms_regs ms) 10 = w64 (sp0 + FO)).
{ rewrite (gv_rd E gv_e1d ms 10 HS), c1_a0, (gv_den_sp E _ HE). unfold w64, FO, OSP_VSN. f_equal. lia. }
assert (R11 : getr (ms_regs ms) 11 = w64 0) by (rewrite (gv_rd E gv_e1d ms 11 HS), c1_a1; reflexivity).
assert (R12 : getr (ms_regs ms) 12 = w64 232) by (rewrite (gv_rd E gv_e1d ms 12 HS), c1_a2; reflexivity).
assert (HspT : spZ (ms_regs ms) = sp0 + FO).
{ unfold spZ. rewrite R2. unfold w64. apply unsigned_lit_small. unfold FO. lia. }
assert (HB1 : snk_base B ly S U W (ms_mem ms) mdX sp0).
{ apply (snk_base_frame B ly S U W mem md sp0 (sp0 + OSP_VSN) (fun a => a = D) (ms_mem ms) mdX gv_base HF);
    [unfold OSP_VSN; lia|].
  intros a ->. pose proof gv_dest as (_ & _ & _ & _ & _ & Ham & _).
  unfold amem_range, kLowMemEnd, SHADOW_OFF, kHighMemBeg, kHighMemEnd in *. lia. }
destruct (band_addressable B ly S U W (ms_mem ms) mdX sp0 (sp0 + FO) 232 HB1 ltac:(unfold FO; lia)
  ltac:(unfold FO; lia) ltac:(unfold FO; lia) eq_refl) as [Hra Hhull].
eapply SRr_bind.
{ apply (kcall W E gv_e1d ms mdX (sp0 + OSP_VSN) gvK gv_e1r [gv_can] 33 RA_MSET (-304) (-304) (-72) ESTACK
    (fun a => sp0 + FO <= a < sp0 + FO + 232)
    (fun regs2 mem2 md2 => ARU tfibsegs B ly S U W mem2 md2 /\
       (forall i, 0 <= i < 232 -> aview tfibsegs (w_H W) mem2 (sp0 + FO + i) = Some 0))
    HS c1_resv E2 eq_refl c1_base c1_lo c1_hi ltac:(rewrite c1_wlo; lia) ltac:(rewrite c1_whi; lia)
    c1_ra c1_sp c1_at c1_wf c1_nc c1_ma c1_ci ltac:(unfold ESTACK; lia) ltac:(unfold gvK, ESTACK; lia) ltac:(lia)
    ltac:(unfold gvK, OSP_VSN; lia) ltac:(unfold OSP_VSN; lia)).
  - intros a Ha _. unfold FO, OSP_VSN in *. lia.
  - intros r a [<-|[]] Ha. unfold gv_can in Ha. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val] in Ha. cbv beta.
    unfold FM_canary, FO, OSP_VSN, ESTACK in *. lia.
  - intros r a [<-|[]] Ha. unfold gv_can in Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. lia.
  - intros a Ha. apply Hp1. unfold snk_band, gvK, OSP_VSN in *. lia.
  - rewrite c1_pc. eapply SRr_mono.
    { apply (AMEMSET ly S U W (ms_regs ms) (ms_mem ms) mdX (sp0 + FO) 0 232).
      - apply (g_ecall_preU B ly S U W (ms_regs ms) (ms_mem ms) mdX HA1).
        + rewrite R1. apply ret_ok_lit; [unfold RA_MSET; lia | reflexivity].
        + rewrite HspT. unfold FO. lia.
        + rewrite HspT. unfold ESTACK, FO in *. lia.
        + rewrite HspT. unfold FO in *. lia.
        + intros a Ha. rewrite HspT in Ha. apply Hp1. unfold snk_band, ESTACK, FO in *. lia.
        + exact R3.
        + exact R4.
      - exact R10.
      - exact R11.
      - exact R12.
      - lia.
      - unfold FO. lia.
      - unfold FO. lia.
      - intros a Ha. rewrite HspT.
        split; [apply apresent_writable; apply Hp1; unfold snk_band, FO in *; lia|].
        split; [apply (ARU_stack tfibsegs B LAWS ly S U W (ms_mem ms) mdX a HA1); unfold FO in *; lia|].
        unfold ESTACK, FO in *. lia.
      - unfold amem_range, kHighMemBeg, kHighMemEnd, FO in *. lia.
      - exact Hra.
      - exact Hhull.
      - exact I. }
    cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HAR2 & HP & Hsbm & _ & Heff & Hfr2 & Hpres2).
    split; [reflexivity|]. exists regs2, mem2, md2.
    split; [unfold cfg_at, raZ; rewrite R1, unsigned_lit_small by (unfold RA_MSET; lia); reflexivity|].
    split; [exact HP|]. split; [exact Hsbm|].
    split.
    { intros a Ha Hb Hx. apply Hfr2; [exact Ha | exact Hx |].
      rewrite HspT. intros C. apply Hb. unfold ESTACK, FO, OSP_VSN in *. lia. }
    split; [exact Hpres2|]. split; [exact HAR2|]. intros i Hi. rewrite (Heff i Hi). reflexivity. }
intros W' c' _ (-> & ms2 & mat2 & -> & HS2 & HP2 & Hfr2 & Hpm2 & HAR2 & HZ2).
assert (HE2 : gvOK (havoc E 33 (map (getr (ms_regs ms2)) CLOB))) by (apply gvOK_havoc; [exact HE | lia]).
assert (HS2' : st_ok tfibsegs (havoc E 33 (map (getr (ms_regs ms2)) CLOB)) gv_s2 (restrict (w_H W) ms2)).
{ apply (gv_st_ok_add _ gv_k1 (restrict (w_H W) ms2) gv_k1r [gv_can] gv_zc HS2 gv_k1_mem c1_zc).
  rewrite c1_kb. cbn [base_val]. rewrite (gvOK_sp _ HE2). unfold gv_zc. apply chunk_ok_zero.
  intros i Hi. change (ms_mem (restrict (w_H W) ms2)) with (mrestrict (w_H W) (ms_mem ms2)). apply AF0x.aview_byte.
  replace (sp0 + OSP_VSN + -304 + i) with (sp0 + FO + i) by (unfold FO, OSP_VSN; lia). exact (HZ2 i Hi). }
assert (HF2 : gvFR (fun a => a = D) (ms_mem ms2) (with_vm_backing (m_vm_lazy mdX) mat2 mdX)).
{ apply (g_frame_step B ly S U W mem md sp0 (sp0 + OSP_VSN) _ (ms_mem ms) mdX (ms_mem ms2) _ HF HAR2
    (with_vm_backing_same mdX mat2)).
  - intros a Ha. apply Hpm2. exact (Hp1 a Ha).
  - intros a Ha Hout Hx. apply Hfr2; [exact Ha | |].
    + intros C. apply Hout. unfold ESTACK, OSP_VSN in *. lia.
    + cbv beta. intros C. apply Hout. unfold FO, OSP_VSN in *. lia.
  - exact Hpm2. }
exact (gv_run2 _ ms2 _ HE2 HS2' HF2).
Qed.

(* ---- the entry: st_ok of gv_s0, the run to the memset call ---- *)
Lemma gv_main : SRr tfibsegs W (cfg_at tfibsegs A_VSN regs mem md) gvQ.
Proof.
gvn.
pose proof HPRE as ((_ & _ & _ & _ & _ & _ & _ & _ & Hband & _) & _ & (cv' & Hgot & _ & _) & _).
assert (EE2 : bv_unsigned (ew gvE0 2) = sp0 + OSP_VSN) by exact (gvOK_sp gvE0 gvOK_E0).
assert (EE32 : bv_unsigned (ew gvE0 32) = cval) by (rewrite (gvOK_can gvE0 gvOK_E0); apply unsigned_lit_small; exact HCV).
assert (EE11 : bv_unsigned (ew gvE0 11) = N).
{ rewrite (gvOK_reg gvE0 11 11%bv gvOK_E0 eq_refl), G11. unfold w64. apply unsigned_lit_small. lia. }
assert (HS0 : st_ok tfibsegs gvE0 gv_s0 (restrict (w_H W) (mkst regs (Z_to_bv 64 A_VSN) mem (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. unfold gv_s0, gvE0. apply (entry_st_ok_full tfibsegs);
    change (Ereg regs [Z_to_bv 64 cval]) with gvE0.
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
    + unfold gv_stk0. apply (region_ok_stack tfibsegs gvE0 _ 2 (sp0 + OSP_VSN) (- gvK)); [exact EE2 | | |].
      * unfold gvK, OSP_VSN in *. lia.
      * unfold OSP_VSN in *. lia.
      * intros a Ha. apply apresent_writable. apply Hband. unfold snk_band, gvK, OSP_VSN in *. lia.
    + unfold gv_got, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      split; [unfold FM_GOT_canary; lia|]. split; [unfold FM_GOT_canary; lia|]. split; [intros o Ho; exfalso; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val tfibsegs gvE0 _ 0 FM_GOT_canary 8 (SLit FM_canary) FM_canary);
        [reflexivity | unfold FM_canary; cbn; lia | cbn; lia | rewrite Z.add_0_l; exact Hgot].
    + unfold gv_can, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      split; [unfold FM_canary; lia|]. split; [unfold FM_canary; lia|]. split; [intros o Ho; exfalso; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val tfibsegs gvE0 _ 0 FM_canary 8 (SOff 32 0) cval);
        [cbn [sv_denot]; rewrite EE32, Z.add_0_r; reflexivity | cbn; lia | cbn; lia | rewrite Z.add_0_l; exact HCAN].
  - apply pairwise_disjoint_of_extents. unfold gv_stk0, gv_got, gv_can, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite EE2.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold gvK, OSP_VSN, FM_canary, FM_GOT_canary in *. repeat split; lia.
  - split; [|split; exact I]. cbn [gv_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite EE2, EE11. change (2 ^ 4) with 16. change (2 ^ 0) with 1.
    repeat split; first [apply Z.mod_1_r | unfold OSP_VSN; lia]. }
unfold cfg_at, w64.
eapply SRr_bind; [exact (g_phase_to W gvE0 W_MEMSET gv_s0 gv_e1 _ _ md HS0 r_gv1)|].
intros W' c' _ (-> & ms1 & mat1 & -> & HS1 & HF1).
pose proof (gv_frame_run _ gvE0 gv_s0 gv_e1 (mkst regs (Z_to_bv 64 A_VSN) mem (seg_rom tfibsegs)) ms1 md mat1
  gv_frame_init gvOK_E0 HS1 HF1 c_w0 c_k1) as HFR1.
exact (gv_call1 gvE0 ms1 _ gvOK_E0 (st_ok_del gvE0 gv_e1 _ [gv_e1r] gv_got [gv_can] HS1 gv_e1_mem) HFR1).
Qed.
End w.

Theorem avsn_ok : avsn_realizes B A_VSN.
Proof.
intros ly S U W regs mem md sp0 D N M f ps P args out HPRE HREGS G10 G11 G12 G13.
pose proof HPRE as (_ & _ & (cval & _ & HCAN & HCV) & _).
exact (gv_main ly S U W regs mem md sp0 D N M f ps P args out cval HPRE HREGS G10 G11 G12 G13 HCAN HCV).
Qed.
End v.
