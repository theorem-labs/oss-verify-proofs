(* reac-pw/fuzz_role image A (fuzz_role.asan, pinned sha256
   614cffc0864cc31d9d1ced61322c4efd567b64bc89fe09a227a05b5126e0debb; every address measured on the unstripped twin
   6da77bafc5c050954dd89149e1e55a24064c2211e3cbd351822d1c0a20900ad6, same loaded bytes): segment S_E01 of the walk of
   LLVMFuzzerTestOneInput, ENTRY 0x7ff88 -> K80194, lib/A/RPgHarn.v rh_S_E01_stmt. Proves no function on its own
   (kind: segment lemma of LLVMFuzzerTestOneInput's walk).

   THE CODE (capstone over image A's loaded segments; lib/A/RPgE01D.v E01_TBL):
     0x7ff88 .. 0x7ffc8  addi sp,sp,-0x1a0; sd zero,0(sp); the 13 saves ra, s0 .. s11 at sp0-8 .. sp0-0x68;
                         addi s0,sp,0x1a0; andi sp,sp,-0x20                                       (run P1a)
     0x7ffcc .. 0x7fff8  mv s1,sp; mv s2,a1; the two .got loads 0x9a888 (the option byte's address) and 0x9a830
                         (the shadow offset's cell); lw a2 (the option byte); ld s7 (the shadow offset K);
                         sd a0,0xc8(s1); beqz a2 (not taken: the byte is 1); a0 = 0x1a0; jal 0x3cbfc     (run P1b)
     __asan_stack_malloc_3(0x1a0): the class-3 frame F (512 bytes), its 64 shadow bytes 0 and its flag pointer
                         word at F + 0x1f8 (YCbq aj_stack_malloc_at over the frame law ASM3)
     0x7fffc .. 0x80190  s6 = s9 = F; bnez s6 (taken: F >= 4096, so the real-stack arm 0x80010 .. 0x80028 and its
                         probe loop are not reached); sd s9,0x110(s1); F[0] = 0x41b58ab3, F[8] = 0x18dbb,
                         F[16] = 0x7ff88; s3 = (F >> 3) + K; the 52 shadow stores 0x8006c .. 0x8013c; the size test
                         `srli a3,s2,0x1a; beqz a3` (taken: n < 2^26); `beqz s2` (n = 0: s5 = 0, R+0x30 = 0);
                         else the flags byte data[0] behind its instrumented check (0x80150 .. 0x80160 and the slow
                         block 0x82610 .. 0x82618), R+0x30 = data[0], R+0xc8 = p + 1, s5 = n - 1; s4 = 0x5000,
                         s2 = a0 = 19744; jal 0x52428                                               (run P2)
     malloc(19744) and K80194: lib/A/RPgE01M.v e01_call_ok.
   THE CHECK AT 0x80158 (`lb a0,0(a0)` of the shadow byte of p, `beqz a0,+8`, `j 0x82610`; `andi a1,a2,7`,
   `bge a1,a0` to the report, `j 0x80164`): the walk loads the shadow byte s of p as memory (a one-byte region at
   (p >> 3) + K, lib/A/RPgMem.v rm_cell_region) and splits both branches. For n >= 8 the shadow byte is 0; for
   1 <= n <= 7 it is n (the input block's last, partial granule), the `beqz` falls through to the slow block, and
   the `bge` is not taken because p mod 8 = 0 < n (rm_A_80158_cell): the error path is not reached.

   THE THEOREM: e01_ok : rh_S_E01_stmt at image A's segments. Its Section hypotheses, each a fact of the runtime's
   symbol record B or of the harness's parameters that another file proves: ASM3 (the class-3 frame law
   astack_malloc_realizes rsegs B 3, lib/A/Rt/StackMalloc3.v), ML and errno_low (the model laws and api_env of
   B), HGOT / HSC / HGU / HUC (the .got words and runtime cells of the shadow offset and the option byte),
   HBsm / HBmalloc (the entries of __asan_stack_malloc_3 and of the malloc trampoline), HAE (the empty input's
   address is in low memory), and RPgE01M.e01_call_ok's own: AMALLOC, HTRACE, HSTK, HEV, HLIVE. *)
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YI16 YM05 YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Pod Require Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import Img0 RPgBase RPgCSpec RPgImgA RPgMem RPgHarn RPgE01D.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require RPgCfgChanges RPgCheckStr RPgSteps.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import RPgE01M.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ======================================== arithmetic ======================================== *)
Lemma e01_land_m32 : forall x, 0 <= x < 2 ^ 64 -> Z.land x (2 ^ 64 - 32) = 32 * (x / 32).
Proof.
intros x Hx.
assert (E1 : 2 ^ 64 - 32 = Z.ldiff (Z.ones 64) (Z.ones 5)) by reflexivity. rewrite E1.
rewrite Z.ldiff_land, Z.land_assoc, <- Z.ldiff_land.
rewrite Z.land_ones, Z.mod_small by lia.
rewrite Z.ldiff_ones_r by lia. rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia. change (2 ^ 5) with 32. lia.
Qed.
(* R = (sp0 - 0x1a0) & -32 *)
Lemma e01_denot_and_m32 : forall E n v c, ew E n = Z_to_bv 64 v -> 0 <= v + c -> v + c < 2 ^ 64 -> 0 <= v < 2 ^ 64 ->
sv_denot E (SAlu ALU_AND (SOff n c) (SLit (-32))) = Z_to_bv 64 (32 * ((v + c) / 32)).
Proof.
intros E n v c Hn H0 H1 Hv. rewrite denot_lit_U. f_equal.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit, (U_atom_off E n v c Hn) by lia.
change (zcanon (-32)) with (2 ^ 64 - 32). rewrite e01_land_m32 by lia. apply zcanon_id. unfold M64.
split; [apply Z.mul_nonneg_nonneg; [lia | apply Z.div_pos; lia]|].
pose proof (Z.mul_div_le (v + c) 32 ltac:(lia)). lia.
Qed.
Lemma e01_R_range : forall S, S mod 16 = 0 -> 0x1a0 <= S ->
S - 0x1b0 <= 32 * ((S - 0x1a0) / 32) <= S - 0x1a0 /\ (32 * ((S - 0x1a0) / 32)) mod 32 = 0 /\
(32 * ((S - 0x1a0) / 32) - S) mod 16 = 0.
Proof.
intros S H16 HS. pose proof (Z.div_mod (S - 0x1a0) 32 ltac:(lia)) as D. pose proof (Z.mod_pos_bound (S - 0x1a0) 32 ltac:(lia)) as M.
pose proof (Z.div_mod S 16 ltac:(lia)) as D16.
assert (HM : (S - 0x1a0) mod 32 = 0 \/ (S - 0x1a0) mod 32 = 16).
{ pose proof (Z.div_mod (S - 0x1a0) 16 ltac:(lia)) as D2.
  assert (Hm16 : (S - 0x1a0) mod 16 = 0) by (rewrite Zminus_mod, H16; reflexivity).
  pose proof (Z.mod_pos_bound (S - 0x1a0) 16 ltac:(lia)).
  assert (Hq : (S - 0x1a0) mod 32 = (S - 0x1a0) mod 16 \/ (S - 0x1a0) mod 32 = (S - 0x1a0) mod 16 + 16).
  { pose proof (Z.div_mod ((S - 0x1a0) / 16) 2 ltac:(lia)). pose proof (Z.mod_pos_bound ((S - 0x1a0) / 16) 2 ltac:(lia)).
    rewrite Z.div_div in * by lia. lia. }
  lia. }
split; [lia|]. split; [rewrite Z.mul_comm, Z_mod_mult; reflexivity|].
replace (32 * ((S - 0x1a0) / 32) - S) with ((2 * ((S - 0x1a0) / 32) - S / 16) * 16) by lia.
apply Z_mod_mult.
Qed.
(* a 4-byte cell read as rd32 *)
Section rd. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma e01_val_mem_of_rd32 : forall H mem a v, 0 <= v < 2 ^ 32 ->
rd32 (aview rsegs H mem) a v -> val_mem rsegs (mrestrict H mem) a 4 v.
Proof.
intros H mem a v Hv Hr k Hk. specialize (Hr k Hk).
unfold aview in Hr. destruct (mbyte rsegs (mrestrict H mem) (a + Z.of_nat k)) as [b|] eqn:Eb; [|discriminate].
cbn [option_map] in Hr. injection Hr as Hr. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned.
lazymatch goal with |- _ = bv_wrap _ ?x => change x with (YG0f.le_byte v 4 k) end. rewrite <- Hr.
symmetry. apply bv_wrap_small. pose proof (bv_unsigned_in_range 8 b) as R. exact R.
Qed.
End rd.

(* ================================ reading a run's last state ================================ *)
Section rdst. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* a register the state holds as an entry atom, or as a literal *)
Lemma e01_reg_atom : forall H E ss ms regs0 extra (r : bv 5) n,
st_ok rsegs E ss (restrict H ms) -> E = Ereg regs0 extra -> sr_get (ss_regs ss) r = SOff n 0 -> (n < 32)%nat ->
getr (ms_regs ms) r = getr regs0 (Z_to_bv 5 (Z.of_nat n)).
Proof.
intros H E ss ms regs0 extra r n HS HE Hsr Hn.
rewrite (st_ok_restrict_reg rsegs H E ss ms r HS), Hsr. apply bv_eq. rewrite denot_SOff, Z.add_0_r, HE.
rewrite (ew_Ereg_nat regs0 extra n (Z_to_bv 5 (Z.of_nat n))).
- apply zcanon_id. pose proof (bv_unsigned_in_range _ (getr regs0 (Z_to_bv 5 (Z.of_nat n)))) as Hb.
  change (bv_modulus 64) with (2 ^ 64) in Hb. unfold M64. lia.
- rewrite Z_to_bv_unsigned. symmetry. apply bv_wrap_small. change (bv_modulus 5) with 32. lia.
Qed.
Lemma e01_reg_lit : forall H E ss ms (r : bv 5) z,
st_ok rsegs E ss (restrict H ms) -> sr_get (ss_regs ss) r = SLit z -> getr (ms_regs ms) r = Z_to_bv 64 z.
Proof. intros H E ss ms r z HS Hsr. rewrite (st_ok_restrict_reg rsegs H E ss ms r HS), Hsr. reflexivity. Qed.
(* the 13 saves, from the chunks of the stack region of P1a's last state *)
Definition e01_cv8 (v : cval) : option nat :=
match v with
| CVal w (SOff i k) => if N.eqb w 8 && (k =? 0) then Some i else None
| _ => None
end.
Lemma e01_cv8_ok : forall v i, e01_cv8 v = Some i -> v = CVal 8 (SOff i 0).
Proof.
intros v i H. unfold e01_cv8 in H.
destruct v as [w e | | |]; try discriminate. destruct e; try discriminate.
lazymatch type of H with (if N.eqb w 8 && (?k =? 0) then Some ?j else None) = Some i =>
  destruct (N.eqb_spec w 8); destruct (Z.eqb_spec k 0); cbn in H; try discriminate; injection H as <-; subst; reflexivity end.
Qed.
Definition e01_save_ok (j : nat) (c : YP09.chunk) : bool :=
(YP09.c_off c =? -8 - 8 * Z.of_nat j) &&
match e01_cv8 (YP09.c_val c) with
| Some i => Z.of_nat i =? bv_unsigned (nth j rh_saved_regs 0%bv)
| None => false
end.
Lemma e01_saves_of_region : forall E (m : word -> option byte) regs0 lo hi wlo whi cs,
region_ok rsegs E m (YP09.mkRegion (Some 2%nat) lo hi wlo whi cs) -> E = Ereg regs0 [] ->
forallb (fun j => existsb (e01_save_ok j) cs) (seq 0 13) = true ->
forall j, (j < 13)%nat ->
val_mem rsegs m (spZ regs0 + (-8 - 8 * Z.of_nat j)) 8 (bv_unsigned (getr regs0 (nth j rh_saved_regs 0%bv))).
Proof.
intros E m regs0 lo hi wlo whi cs Hreg HE Hck j Hj.
assert (Hin : In j (seq 0 13)) by (apply in_seq; lia).
pose proof (proj1 (forallb_forall _ _) Hck j Hin) as Hx. apply existsb_exists in Hx as ([off v] & Hc & Hok).
unfold e01_save_ok in Hok. cbn [YP09.c_off YP09.c_val] in Hok.
apply andb_prop in Hok as [Hoff Hok]. apply Z.eqb_eq in Hoff. subst off.
destruct (e01_cv8 v) as [i|] eqn:Ev; [|discriminate]. apply e01_cv8_ok in Ev. subst v.
apply Z.eqb_eq in Hok. rename Hok into Hi.
assert (Hi5 : Z_to_bv 5 (Z.of_nat i) = nth j rh_saved_regs 0%bv).
{ apply bv_eq. rewrite Z_to_bv_unsigned, Hi. apply bv_wrap_small. apply bv_unsigned_in_range. }
pose proof (RPgCheckStr.field_of_region E m 2 (spZ regs0) cs lo hi wlo whi (-8 - 8 * Z.of_nat j) 8 (SOff i 0)
  (bv_unsigned (getr regs0 (nth j rh_saved_regs 0%bv))) Hreg) as HF.
apply HF.
- rewrite HE, (ew_Ereg_nat regs0 [] 2 2%bv eq_refl). reflexivity.
- exact Hc.
- apply bv_eq. rewrite denot_SOff, Z.add_0_r, HE, Z_to_bv_bv_unsigned.
  assert (Hi32 : (i < 32)%nat).
  { pose proof (bv_unsigned_in_range _ (nth j rh_saved_regs 0%bv)) as Hb. change (bv_modulus 5) with 32 in Hb. lia. }
  rewrite (ew_Ereg_nat regs0 [] i (Z_to_bv 5 (Z.of_nat i))), Hi5.
  + apply zcanon_id. pose proof (bv_unsigned_in_range _ (getr regs0 (nth j rh_saved_regs 0%bv))) as Hb.
    change (bv_modulus 64) with (2 ^ 64) in Hb. unfold M64. lia.
  + rewrite Z_to_bv_unsigned. symmetry. apply bv_wrap_small. change (bv_modulus 5) with 32. lia.
- pose proof (bv_unsigned_in_range _ (getr regs0 (nth j rh_saved_regs 0%bv))) as Hb.
  change (bv_modulus 64) with (2 ^ 64) in Hb. exact Hb.
- cbn. lia.
Qed.
(* the frame's 52 shadow bytes, from the chunks of its region (the stores leave each as the low byte of a
   sign-extended literal) *)
Definition e01_cvlit1 (v : cval) : option Z :=
match v with
| CVal w (SLit z) => if N.eqb w 1 then Some z else None
| _ => None
end.
Lemma e01_cvlit1_ok : forall v z, e01_cvlit1 v = Some z -> v = CVal 1 (SLit z).
Proof.
intros v z H. unfold e01_cvlit1 in H.
destruct v as [w e | | |]; try discriminate. destruct e; try discriminate.
lazymatch type of H with (if N.eqb w 1 then Some ?j else None) = Some z =>
  destruct (N.eqb_spec w 1); cbn in H; try discriminate; injection H as <-; subst; reflexivity end.
Qed.
Definition e01_sh_ok (pat : list Z) (i : nat) (c : YP09.chunk) : bool :=
(YP09.c_off c =? Z.of_nat i) &&
match e01_cvlit1 (YP09.c_val c) with
| Some z => bv_unsigned (byte_of_word (Z_to_bv 64 z) 0) =? nth i pat 0
| None => false
end.
Lemma e01_fsh_of_region : forall E H mem (k : nat) F lo hi wlo whi cs pat,
region_ok rsegs E (mrestrict H mem) (YP09.mkRegion (Some k) lo hi wlo whi cs) ->
bv_unsigned (ew E k) = shadow_addr F ->
forallb (fun i => existsb (e01_sh_ok pat i) cs) (seq 0 (length pat)) = true ->
rl_fsh rsegs H mem F pat.
Proof.
intros E H mem k F lo hi wlo whi cs pat (_ & _ & _ & Hcs) Hb Hck i Hi.
assert (Hin : In (Z.to_nat i) (seq 0 (length pat))) by (apply in_seq; lia).
pose proof (proj1 (forallb_forall _ _) Hck _ Hin) as Hx. apply existsb_exists in Hx as ([off v] & Hc & Hok).
unfold e01_sh_ok in Hok. cbn [YP09.c_off YP09.c_val] in Hok.
apply andb_prop in Hok as [Hoff Hok]. apply Z.eqb_eq in Hoff. rewrite Z2Nat.id in Hoff by lia. subst off.
destruct (e01_cvlit1 v) as [z|] eqn:Ev; [|discriminate]. apply e01_cvlit1_ok in Ev. subst v.
apply Z.eqb_eq in Hok.
pose proof (proj1 (Forall_forall _ _) Hcs _ Hc) as Hck1. cbn [YP09.r_base base_val] in Hck1. rewrite Hb in Hck1.
destruct (Hck1 0 ltac:(cbn; lia)) as (b & Hcb & Hmb). cbn [cbyte YP09.c_off YP09.c_val sv_denot] in Hcb, Hmb.
injection Hcb as <-. rewrite Z.add_0_r in Hmb. unfold aview. rewrite Hmb. cbn [option_map]. rewrite Hok. reflexivity.
Qed.
(* a run keeps every byte outside the write windows of its regions *)
Lemma e01_keep_frame : forall E rs H (m m' : word -> option byte) (P : Z -> Prop),
frame_of E rs (mrestrict H m) (mrestrict H m') -> (forall a, in_wrange E rs a -> P a) ->
forall a, 0 <= a < 2 ^ 64 -> ~ P a -> aview rsegs H m' a = aview rsegs H m a.
Proof.
intros E rs H m m' P HF HW a Ha Hz. unfold aview, mbyte.
rewrite (HF (Z_to_bv 64 a)); [reflexivity|]. rewrite unsigned_lit_small by exact Ha. intros X. exact (Hz (HW a X)).
Qed.
Lemma e01_val_mem_keep : forall H (m m' : word -> option byte) a (n : nat) v,
(forall k, 0 <= k < Z.of_nat n -> aview rsegs H m' (a + k) = aview rsegs H m (a + k)) ->
val_mem rsegs (mrestrict H m) a n v -> val_mem rsegs (mrestrict H m') a n v.
Proof. intros H m m' a n v K V. exact (val_mem_kept rsegs H H m m' a n v K V). Qed.
(* ---- the last state's registers and cells, at any value the atoms give ---- *)
Lemma e01_reg_off : forall H E ss ms (r : bv 5) n c v,
st_ok rsegs E ss (restrict H ms) -> sr_get (ss_regs ss) r = SOff n c ->
bv_unsigned (ew E n) + c = v -> getr (ms_regs ms) r = w64 v.
Proof.
intros H E ss ms r n c v HS Hsr Hu.
rewrite (st_ok_restrict_reg rsegs H E ss ms r HS), Hsr, denot_lit_U, U_SOff, Hu. unfold w64. apply Z_to_bv64_canon.
Qed.
Lemma e01_reg_lit2 : forall H E ss ms (r : bv 5) z v,
st_ok rsegs E ss (restrict H ms) -> sr_get (ss_regs ss) r = SLit z -> z = v -> getr (ms_regs ms) r = w64 v.
Proof. intros H E ss ms r z v HS Hsr <-. exact (e01_reg_lit H E ss ms r z HS Hsr). Qed.
Lemma e01_cell_off : forall E m k base cs lo hi wlo whi off n c v,
region_ok rsegs E m (YP09.mkRegion (Some k) lo hi wlo whi cs) -> bv_unsigned (ew E k) = base ->
In (YP09.mkChunk off (CVal 8 (SOff n c))) cs -> bv_unsigned (ew E n) + c = v ->
val_mem rsegs m (base + off) 8 (v mod 2 ^ 64).
Proof.
intros E m k base cs lo hi wlo whi off n c v Hreg Hb Hc Hv.
apply (RPgCheckStr.field_of_region E m k base cs lo hi wlo whi off 8 (SOff n c) (v mod 2 ^ 64) Hreg Hb Hc).
- apply bv_eq. rewrite denot_SOff, Hv, Z_to_bv_unsigned. unfold zcanon, M64, bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  rewrite Z.mod_mod by lia. reflexivity.
- change (8 * Z.of_N 8) with 64. apply Z.mod_pos_bound. lia.
- lia.
Qed.
Lemma e01_cell_lit : forall E m k base cs lo hi wlo whi off z v,
region_ok rsegs E m (YP09.mkRegion (Some k) lo hi wlo whi cs) -> bv_unsigned (ew E k) = base ->
In (YP09.mkChunk off (CVal 8 (SLit z))) cs -> z = v ->
val_mem rsegs m (base + off) 8 (v mod 2 ^ 64).
Proof.
intros E m k base cs lo hi wlo whi off z v Hreg Hb Hc <-.
apply (RPgCheckStr.field_of_region E m k base cs lo hi wlo whi off 8 (SLit z) (z mod 2 ^ 64) Hreg Hb Hc).
- apply bv_eq. cbn [sv_denot]. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  rewrite Z.mod_mod by lia. reflexivity.
- change (8 * Z.of_N 8) with 64. apply Z.mod_pos_bound. lia.
- lia.
Qed.
Lemma e01_val_mem_mod64 : forall m a v, val_mem rsegs m a 8 v -> val_mem rsegs m a 8 (v mod 2 ^ 64).
Proof.
intros m a v V k Hk. rewrite (V k Hk). unfold YO0f.le_byte. change (8 * Z.of_nat 8) with 64.
rewrite Z.mod_mod by lia. reflexivity.
Qed.
(* the carried cells from the 13 saves and the flag pointer word *)
Lemma e01_kept_of : forall (hx : rh_hcx rsegs) pos e (W' : world rsegs) mem' regs',
(forall j, (j < 13)%nat -> val_mem rsegs (mrestrict (w_H W') mem') (e_S e + (-8 - 8 * Z.of_nat j)) 8
  (bv_unsigned (getr (h_regs rsegs hx) (nth j rh_saved_regs 0%bv)))) ->
val_mem rsegs (mrestrict (w_H W') mem') (e_F e + 0x1f8) 8 (flag_addr (h_ly rsegs hx) RH_CID pos) ->
rh_kept rsegs hx pos e W' mem' regs'.
Proof.
intros hx pos e W' mem' regs' HS HFl. unfold rh_kept, rh_cells, rh_saves_L. apply Forall_app. split.
- apply Forall_forall. intros f Hf. apply in_map_iff in Hf as (j & <- & Hj). apply in_seq in Hj.
  cbn [fst snd rl_at rl_xv]. rewrite e01m_umod. apply HS. lia.
- constructor; [|constructor]. cbn [fst snd rl_at rl_xv]. apply e01_val_mem_mod64. exact HFl.
Qed.
(* the input after its first byte *)
Lemma e01_garr8_tl : forall m a x l, garr8 rsegs m a (x :: l) -> garr8 rsegs m (a + 1) l.
Proof.
intros m a x l G j Hj. destruct (G (S j) ltac:(cbn; lia)) as [V Hb]. cbn [nth] in V, Hb. split; [|exact Hb].
replace (a + 1 + Z.of_nat j) with (a + Z.of_nat (S j)) by lia. exact V.
Qed.
Lemma e01_garr8_keep : forall H H' m m' a l, garr8 rsegs (mrestrict H m) a l ->
(forall j, (j < length l)%nat -> aview rsegs H' m' (a + Z.of_nat j) = aview rsegs H m (a + Z.of_nat j)) ->
garr8 rsegs (mrestrict H' m') a l.
Proof.
intros H H' m m' a l G K j Hj. destruct (G j Hj) as [V Hb]. split; [|exact Hb].
apply (val_mem_kept rsegs H H' m m' (a + Z.of_nat j) 1 _); [|exact V].
intros k Hk. replace k with 0 by (cbn in Hk; lia). rewrite Z.add_0_r. exact (K j Hj).
Qed.
(* the index of the region whose base is atom k *)
Fixpoint e01_find_base (rs : smem) (k : nat) : nat :=
match rs with
| [] => O
| r :: rs' => match YP09.r_base r with Some k' => if Nat.eqb k k' then O else S (e01_find_base rs' k)
              | None => S (e01_find_base rs' k) end
end.
End rdst.
(* P2's write windows: the real-frame slots, the frame's header, its 52 shadow bytes *)
Definition e01_p2win (R F a : Z) : Prop :=
(R + 0x30 <= a < R + 0x118) \/ (F <= a < F + 24) \/ (shadow_addr F <= a < shadow_addr F + 52).
(* the windows of a run of P2 lie in e01_p2win: every region of the state is one of P2's three or a read-only one *)
Ltac e01_win2 U9 U10 U33 :=
  let a := fresh "a" in let r := fresh "r" in let Hin := fresh "Hin" in let Ha := fresh "Ha" in
  intros a (r & Hin & Ha);
  lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end;
  repeat (destruct Hin as [<- | Hin];
    [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
      first [ rewrite U9 in Ha | rewrite U10 in Ha | rewrite U33 in Ha | idtac ];
      unfold e01_p2win; revert Ha; clear; intros Ha; lia | ]);
  destruct Hin.
(* compose a run's keep with the keep so far, from the memory after the frame call (KP2) *)
Ltac e01_keep2 HFr KP2 R F U9 U10 U33 :=
  lazymatch type of HFr with frame_of ?E ?rs (mrestrict ?H ?m0) (mrestrict _ ?m1) =>
  lazymatch type of KP2 with forall a, _ -> _ -> aview _ _ ?mx a = aview _ _ ?mb a =>
  let K := fresh "K" in let K2 := fresh "K" in
  assert (K : forall a, 0 <= a < 2 ^ 64 -> ~ e01_p2win R F a -> aview rsegs H m1 a = aview rsegs H m0 a)
    by (apply (e01_keep_frame E rs H m0 m1 _ HFr); e01_win2 U9 U10 U33);
  assert (K2 : forall a, 0 <= a < 2 ^ 64 -> ~ e01_p2win R F a -> aview rsegs H m1 a = aview rsegs H mb a)
    by (let a := fresh "a" in let Ha := fresh "Ha" in let Hn := fresh "Hn" in
        intros a Ha Hn; rewrite (K a Ha Hn); exact (KP2 a Ha Hn));
  clear K KP2; rename K2 into KP2 end end.

(* ======================================== the run P1a ======================================== *)
(* the entry: the stack window [sp0 - 0x1b0, sp0) the prologue writes (the saves, `sd zero,0(sp)` at sp0 - 0x1a0) *)
Definition e01_p1a_rs : smem := [ YP09.mkRegion (Some 2%nat) (-0x1b0) 0 (-0x1b0) 0 [] ].
Definition e01_p1a_facts : facts := mkFacts [ (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4) ] [] [].
Definition e01_p1a_ss : sstate := mkSS E01_A sr_atoms e01_p1a_rs None e01_p1a_facts.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variables RLO RHI RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK : Z.
Hypothesis HSTK : 0x1b0 + ASTACK <= LLVMF_STK.

Lemma e01_p1a_entry : forall (W : world rsegs) regs mem,
(forall a, spZ regs - 0x1b0 <= a < spZ regs -> apresent (w_H W) mem a) ->
2 ^ 46 <= spZ regs <= 2 ^ 47 -> spZ regs mod 16 = 0 ->
st_ok rsegs (Ereg regs []) e01_p1a_ss (restrict (w_H W) (mkst regs (Z_to_bv 64 E01_A) mem (seg_rom rsegs))).
Proof.
intros W regs mem Hpres Hsp Hal.
rewrite restrict_mkst_fx.
set (E := Ereg regs []).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (subst E; rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
unfold e01_p1a_ss. apply (entry_st_ok_full rsegs); change (Ereg regs []) with E.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- unfold e01_p1a_rs. apply Forall_cons; [|apply Forall_nil].
  unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Usp.
  split; [lia|]. split; [lia|]. split; [|constructor]. intros o Ho. apply (apresent_writable rsegs). apply Hpres. lia.
- apply pairwise_disjoint_of_extents. cbn. tauto.
- split; [|split; [exact I | exact I]]. cbn [e01_p1a_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite Usp. change (2 ^ 4) with 16. repeat split; lia.
Qed.

(* ======================================== the run P1b ========================================
   From 0x7ffcc with sp = R (atom 2): the slot R+0xc8 the cursor is stored to, the two .got words and the two
   runtime cells they point to (AR's const law: the shadow offset's cell holds K, the option byte's cell holds 1). *)
Definition E01_GOT_UAR : Z := 0x9a888.
Definition E01_GOT_SH : Z := 0x9a830.
Definition E01_UAR : Z := 0xa3400.
Definition E01_SHC : Z := 0xa33f8.
Definition e01_p1b_rs : smem := [
  YP09.mkRegion (Some 2%nat) 0xc8 0xd0 0xc8 0xd0 [];
  YP09.mkRegion None E01_GOT_UAR (E01_GOT_UAR + 8) 0 0 [YP09.mkChunk E01_GOT_UAR (CVal 8 (SLit E01_UAR))];
  YP09.mkRegion None E01_GOT_SH (E01_GOT_SH + 8) 0 0 [YP09.mkChunk E01_GOT_SH (CVal 8 (SLit E01_SHC))];
  YP09.mkRegion None E01_UAR (E01_UAR + 4) 0 0 [YP09.mkChunk E01_UAR (CVal 4 (SLit 1))];
  YP09.mkRegion None E01_SHC (E01_SHC + 8) 0 0 [YP09.mkChunk E01_SHC (CVal 8 (SLit SHADOW_OFF))] ].
Definition E01_P1B : Z := 0x7ffcc.
Definition e01_p1b_facts : facts := mkFacts [ (2%nat, mkAF (2 ^ 46 - 512) (2 ^ 47) 5) ] [] [].
Definition e01_p1b_ss : sstate := mkSS E01_P1B sr_atoms e01_p1b_rs None e01_p1b_facts.

Lemma e01_p1b_entry : forall (W : world rsegs) regs mem,
(forall a, spZ regs + 0xc8 <= a < spZ regs + 0xd0 -> apresent (w_H W) mem a) ->
2 ^ 46 - 512 <= spZ regs <= 2 ^ 47 -> spZ regs mod 32 = 0 ->
rdword (aview rsegs (w_H W) mem) E01_GOT_UAR = Some E01_UAR ->
rdword (aview rsegs (w_H W) mem) E01_GOT_SH = Some E01_SHC ->
rd32 (aview rsegs (w_H W) mem) E01_UAR 1 ->
rdword (aview rsegs (w_H W) mem) E01_SHC = Some SHADOW_OFF ->
st_ok rsegs (Ereg regs []) e01_p1b_ss (restrict (w_H W) (mkst regs (Z_to_bv 64 E01_P1B) mem (seg_rom rsegs))).
Proof.
intros W regs mem Hpres Hsp Hal K1 K2 K3 K4.
rewrite restrict_mkst_fx.
set (E := Ereg regs []).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (subst E; rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
unfold e01_p1b_ss. apply (entry_st_ok_full rsegs); change (Ereg regs []) with E.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- unfold e01_p1b_rs. repeat apply Forall_cons; try apply Forall_nil;
  unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  + rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable rsegs). apply Hpres. lia.
  + split; [unfold E01_GOT_UAR; lia|]. split; [unfold E01_GOT_UAR; lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor]. rewrite <- (Z.add_0_l E01_GOT_UAR) at 1.
    apply (chunk_ok_val rsegs E _ 0 E01_GOT_UAR 8 (SLit E01_UAR) E01_UAR); [reflexivity | unfold E01_UAR; zside | zside |].
    exact (val_mem_of_rdword rsegs (w_H W) mem _ _ K1).
  + split; [unfold E01_GOT_SH; lia|]. split; [unfold E01_GOT_SH; lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor]. rewrite <- (Z.add_0_l E01_GOT_SH) at 1.
    apply (chunk_ok_val rsegs E _ 0 E01_GOT_SH 8 (SLit E01_SHC) E01_SHC); [reflexivity | unfold E01_SHC; zside | zside |].
    exact (val_mem_of_rdword rsegs (w_H W) mem _ _ K2).
  + split; [unfold E01_UAR; lia|]. split; [unfold E01_UAR; lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor]. rewrite <- (Z.add_0_l E01_UAR) at 1.
    apply (chunk_ok_val rsegs E _ 0 E01_UAR 4 (SLit 1) 1); [reflexivity | zside | zside |].
    exact (e01_val_mem_of_rd32 (w_H W) mem E01_UAR 1 ltac:(lia) K3).
  + split; [unfold E01_SHC; lia|]. split; [unfold E01_SHC; lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor]. rewrite <- (Z.add_0_l E01_SHC) at 1.
    apply (chunk_ok_val rsegs E _ 0 E01_SHC 8 (SLit SHADOW_OFF) SHADOW_OFF); [reflexivity | unfold SHADOW_OFF; zside | zside |].
    exact (val_mem_of_rdword rsegs (w_H W) mem _ _ K4).
- apply pairwise_disjoint_of_extents.
  unfold e01_p1b_rs, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite Usp.
  unfold E01_GOT_UAR, E01_GOT_SH, E01_UAR, E01_SHC.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  revert Hsp. clear. intros. repeat split; lia.
- split; [|split; [exact I | exact I]]. cbn [e01_p1b_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite Usp. change (2 ^ 5) with 32. repeat split; lia.
Qed.

(* ======================================== the run P2 ========================================
   From 0x7fffc, after the frame call: a0 = F, s1 = R, s2 = n, s7 = K. The regions: the real-frame slots
   [R+0x30, R+0x118) (s1, atom 9; the cursor p at R+0xc8, atom 32), the frame's header words [F, F+24) (a0,
   atom 10) and its 52 shadow bytes from (F >> 3) + K (atom 33, with the alias the code's `srli s3,s9,3` /
   `add s3,s3,s7` forms). The input's first byte and its shadow byte (atoms 34 .. 36) are regions only once the
   walk knows n > 0. *)
Definition e01_p2_extra (p F s b : Z) : list word :=
  [w64 p; w64 (shadow_addr F); w64 (shadow_of_addr SHADOW_OFF p); w64 s; w64 b].
Definition e01_p2_rs : smem := [
  YP09.mkRegion (Some 9%nat) 0x30 0x118 0x30 0x118 [YP09.mkChunk 0xc8 (CVal 8 (SOff 32 0))];
  YP09.mkRegion (Some 10%nat) 0 24 0 24 [];
  YP09.mkRegion (Some 33%nat) 0 52 0 52 [] ].
Definition e01_p2_facts : facts :=
  mkFacts [ (10%nat, mkAF 4096 (2 ^ 47) 5); (18%nat, mkAF 0 (2 ^ 26 - 1) 0) ] [] [].
Definition e01_p2_ss : sstate := mkSS E01_SM3_RA sr_atoms e01_p2_rs None e01_p2_facts.

Lemma e01_p2_entry : forall (W : world rsegs) regs3 mem3 R F n p s b,
getr regs3 9 = w64 R -> getr regs3 10 = w64 F -> getr regs3 18 = w64 n ->
0 <= R -> R + 0x118 <= 2 ^ 64 -> 4096 <= F -> F + 512 <= 2 ^ 47 -> F mod 32 = 0 -> 0 <= n < 2 ^ 26 ->
0 <= p < 2 ^ 64 ->
(forall a, R + 0x30 <= a < R + 0x118 -> apresent (w_H W) mem3 a) ->
(forall a, F <= a < F + 24 -> apresent (w_H W) mem3 a) ->
(forall i, 0 <= i < 52 -> apresent (w_H W) mem3 (shadow_addr F + i)) ->
val_mem rsegs (mrestrict (w_H W) mem3) (R + 0xc8) 8 p ->
zpairwise_disjoint [(R + 0x30, R + 0x118); (F, F + 24); (shadow_addr F, shadow_addr F + 52)] ->
st_ok rsegs (Ereg regs3 (e01_p2_extra p F s b)) e01_p2_ss
  (restrict (w_H W) (mkst regs3 (Z_to_bv 64 E01_SM3_RA) mem3 (seg_rom rsegs))).
Proof.
intros W regs3 mem3 R F n p s b H9 H10 H18 HR0 HR1 HF0 HF1 HF32 Hn Hp PR PF PSh Vp Hdisj.
rewrite restrict_mkst_fx.
set (E := Ereg regs3 (e01_p2_extra p F s b)).
assert (U9 : bv_unsigned (ew E 9) = R).
{ subst E. rewrite (ew_Ereg_nat regs3 _ 9 9%bv eq_refl), H9. unfold w64. apply unsigned_lit_small. lia. }
assert (U10 : bv_unsigned (ew E 10) = F).
{ subst E. rewrite (ew_Ereg_nat regs3 _ 10 10%bv eq_refl), H10. unfold w64. apply unsigned_lit_small. lia. }
assert (U18 : bv_unsigned (ew E 18) = n).
{ subst E. rewrite (ew_Ereg_nat regs3 _ 18 18%bv eq_refl), H18. unfold w64. apply unsigned_lit_small. lia. }
assert (HshF : 0 <= shadow_addr F < 2 ^ 45).
{ revert HF0 HF1. clear. intros. unfold shadow_addr, SHADOW_OFF.
  split; [apply Z.add_nonneg_nonneg; [lia | apply Z.div_pos; lia]|].
  assert (F / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; lia). lia. }
assert (U33 : bv_unsigned (ew E 33) = shadow_addr F).
{ subst E. rewrite (ew_Ereg_extra regs3 _ 1). cbn [nth e01_p2_extra]. unfold w64. apply unsigned_lit_small. lia. }
assert (D32 : sv_denot E (SOff 32 0) = Z_to_bv 64 p).
{ apply bv_eq. rewrite denot_SOff, Z.add_0_r. subst E. rewrite (ew_Ereg_extra regs3 _ 0). cbn [nth e01_p2_extra].
  unfold w64. rewrite !unsigned_lit_small by lia. apply zcanon_id. unfold M64. lia. }
unfold e01_p2_ss. apply (entry_st_ok_full rsegs); change (Ereg regs3 (e01_p2_extra p F s b)) with E.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- unfold e01_p2_rs. repeat apply Forall_cons; try apply Forall_nil;
  unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  + rewrite U9. split; [lia|]. split; [lia|]. split.
    * intros o Ho. apply (apresent_writable rsegs). apply PR. lia.
    * constructor; [|constructor].
      apply (chunk_ok_val rsegs E _ R 0xc8 8 (SOff 32 0) p D32); [cbn; lia | cbn; lia | exact Vp].
  + rewrite U10. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable rsegs). apply PF. lia.
  + rewrite U33. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable rsegs). apply PSh. lia.
- apply pairwise_disjoint_of_extents.
  unfold e01_p2_rs, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U10, U33.
  rewrite !Z.add_0_r. exact Hdisj.
- split; [|split; [exact I | exact I]]. cbn [e01_p2_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite U10, U18. change (2 ^ 5) with 32. rewrite Z.pow_0_r, Z.mod_1_r. repeat split; lia.
Qed.

Hypothesis ASM3 : astack_malloc_realizes rsegs B 3.
Hypothesis ML : model_laws (as_universe B).
Hypothesis errno_low : api_env rsegs B.
(* the symbol record's cells and code entries (the relocated frame's TfibLib / TfibSyms fields) *)
Hypothesis HGOT : as_got_shadow B = 0x9a830.
Hypothesis HSC : as_shadow_cell B = 0xa33f8.
Hypothesis HGU : as_got_uar B = 0x9a888.
Hypothesis HUC : as_uar_cell B = 0xa3400.
Hypothesis HBsm : pc_stack_malloc (as_code B) 3 = E01_SM3.
(* the empty input's address (the harness's caller passes it when n = 0) *)
Hypothesis HAE : 0 < A_EMPTY < kLowMemEnd.
(* the malloc(pp) call (lib/A/RPgE01M.v e01_call_ok's own hypotheses) *)
Hypothesis AMALLOC : amalloc_realizes rsegs B.
Hypothesis HBmalloc : pc_wrap_malloc (as_code B) = E01_MALLOC.
Hypothesis HTRACE : e01_trace_stmt B RA_LLVMF.
Hypothesis HEV : 1 <= EV_LIB.
Hypothesis HLIVE : Layout.PP_SIZE <= LIVE_LIB.

(* the input after the flags byte: nothing (n = 0), or data[1 .. n) *)
Lemma e01_in_nil : forall (hx : rh_hcx rsegs) W mem e, e_left e = 0 -> e_len e = rl_len [] -> 0 < e_src e ->
e_src e < kLowMemEnd -> e01_in B hx W mem e [].
Proof.
intros hx W mem e H1 H2 H3 H4. unfold e01_in. cbn [length Z.of_nat map].
split; [exact H1|]. split; [exact H2|]. split; [apply garr8_nil|]. split; [exact H3|].
rewrite H1. unfold amem_range, kLowMemEnd in *. split; [lia|]. split; [left; lia|]. left; reflexivity.
Qed.
Lemma e01_in_cons : forall (hx : rh_hcx rsegs) W mem e rest p n,
In (p, n) (ablocks B (h_ly rsegs hx) (h_S rsegs hx)) ->
e_src e = p + 1 -> e_left e = n - 1 -> n = Z.of_nat (S (length rest)) -> e_len e = rl_len rest ->
garr8 rsegs (mrestrict (w_H W) mem) (p + 1) (map (fun x : byte => bv_unsigned x) rest) ->
0 < p -> p + n <= 2 ^ 63 -> amem_range p n ->
e01_in B hx W mem e rest.
Proof.
intros hx W mem e rest p n Hin Hs Hl Hn Hle G Hp Hpn Ham. unfold e01_in. rewrite Hs, Hl.
pose proof (req_size_pos n ltac:(lia)) as [_ Hrq].
split; [lia|]. split; [exact Hle|]. split; [exact G|]. split; [lia|]. split; [lia|].
split; [unfold amem_range in *; lia|]. right. exists p, n. split; [exact Hin|]. lia.
Qed.

Ltac e01_Urw := repeat match goal with H : bv_unsigned (ew ?E ?k) = _ |- context [bv_unsigned (ew ?E ?k)] => rewrite H end.
Ltac e01_val := cbn [e_S e_R e_F e_pp e_pod e_len e_fl e_src e_left];
  first [reflexivity | ring | (vm_compute; reflexivity)].
Ltac e01_greg := match goal with Hg : getr ?rg _ = _ |- getr ?rg _ = _ => exact Hg end.
Ltac e01_reg HS :=
  lazymatch goal with |- getr (ms_regs ?ms) ?r = w64 ?v =>
  lazymatch type of HS with st_ok _ ?E ?ss (restrict ?H _) =>
  let regs3 := lazymatch E with Ereg ?rg _ => rg end in
  let x := eval vm_compute in (sr_get (ss_regs ss) r) in
  match x with
  | SLit ?z => apply (e01_reg_lit2 H E ss ms r z v HS ltac:(vm_compute; reflexivity)); e01_val
  | SOff ?k 0 => (lazymatch eval vm_compute in (Nat.ltb k 32) with true => idtac end);
      rewrite (e01_reg_atom H E ss ms regs3 _ r k HS eq_refl ltac:(vm_compute; reflexivity)
        ltac:(apply Nat.ltb_lt; vm_compute; reflexivity)); e01_greg
  | SOff ?k ?c => apply (e01_reg_off H E ss ms r k c v HS ltac:(vm_compute; reflexivity)); e01_Urw; e01_val
  end end end.
Ltac e01_inchunk := vm_compute; repeat (first [left; reflexivity | right]).
Ltac e01_cell RG :=
  lazymatch type of RG with region_ok _ ?E ?m (YP09.mkRegion (Some ?k) ?lo ?hi ?wlo ?whi ?cs) =>
  lazymatch goal with |- val_mem _ _ (?b + ?off) 8 (?v mod 2 ^ 64) =>
  let c := eval vm_compute in (find_chunk cs off 8) in
  lazymatch c with
  | Some (YP09.mkChunk _ (CVal _ (SOff ?na ?cc))) =>
      apply (e01_cell_off E m k b cs lo hi wlo whi off na cc v RG); [e01_Urw; reflexivity | e01_inchunk | e01_Urw; e01_val]
  | Some (YP09.mkChunk _ (CVal _ (SLit ?z))) =>
      apply (e01_cell_lit E m k b cs lo hi wlo whi off z v RG); [e01_Urw; reflexivity | e01_inchunk | e01_val]
  end end end.
(* At the malloc entry 0x52428: the call state e01_call_facts, then e01_call_ok. *)
Ltac e01_fin HS HJ KP2 e rest W F mem3 HB Eab3 U33 SAV3 NWsav FLG3 NWflg :=
  let msT := lazymatch type of HS with st_ok _ _ _ (restrict _ ?m) => m end in
  let hx := lazymatch goal with |- SRr _ _ _ (rh_at_C1 _ _ _ ?h) => h end in
  rewrite (st_ok_restrict_mkst rsegs _ _ _ msT HS eq_refl); cbn [ss_pc];
  eapply (e01_call_ok B RLO RHI RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK errno_low ML AMALLOC HBmalloc HTRACE HSTK HEV HLIVE
    hx _ e rest _ _ _ (ms_regs msT) (ms_mem msT) _ HB);
  unfold e01_call_facts;
  let ss := lazymatch type of HS with st_ok _ _ ?s _ => s end in
  let E := lazymatch type of HS with st_ok _ ?E' _ _ => E' end in
  let i9 := eval vm_compute in (e01_find_base (ss_mem ss) 9) in
  let i33 := eval vm_compute in (e01_find_base (ss_mem ss) 33) in
  let r9 := eval vm_compute in (nth_error (ss_mem ss) i9) in
  let r33 := eval vm_compute in (nth_error (ss_mem ss) i33) in
  let RG9 := fresh "RG9" in let RG33 := fresh "RG33" in
  lazymatch r9 with Some ?rg9 => lazymatch r33 with Some ?rg33 =>
  pose proof (RPgCheckStr.st_ok_region_nth _ E ss msT i9 rg9 HS ltac:(vm_compute; reflexivity)) as RG9;
  pose proof (RPgCheckStr.st_ok_region_nth _ E ss msT i33 rg33 HS ltac:(vm_compute; reflexivity)) as RG33
  end end;
  split; [exact HJ|];
  split; [exact Eab3|];
  split; [split; [reflexivity | split; reflexivity]|];
  split; [e01_reg HS|]; split; [e01_reg HS|]; split; [e01_reg HS|]; split; [e01_reg HS|]; split; [e01_reg HS|];
  split; [unfold rl_cut; cbn [tl hi_L1 role_himg_A];
          repeat (apply Forall_cons; [cbn [fst snd rl_at rl_xv]; first [e01_reg HS | e01_cell RG9] |]); apply Forall_nil|];
  split; [apply (e01_fsh_of_region E _ _ 33 F _ _ _ _ _ role_A_shA RG33 U33); vm_compute; reflexivity|];
  split; [|split; [apply e01_kept_of;
    [ let j := fresh "j" in let Hj := fresh "Hj" in let k := fresh "k" in let Hk := fresh "Hk" in
      let Hb := fresh "Hb" in let Hn := fresh "Hn" in
      intros j Hj; apply (e01_val_mem_keep (w_H W) mem3 (ms_mem msT)); [|exact (SAV3 j Hj)];
      intros k Hk; cbn in Hk; destruct (NWsav j k Hj Hk) as [Hb Hn]; exact (KP2 _ Hb Hn)
    | let k := fresh "k" in let Hk := fresh "Hk" in let Hb := fresh "Hb" in let Hn := fresh "Hn" in
      apply (e01_val_mem_keep (w_H W) mem3 (ms_mem msT)); [|exact FLG3];
      intros k Hk; cbn in Hk; destruct (NWflg k Hk) as [Hb Hn]; exact (KP2 _ Hb Hn) ] |]].
Ltac e01_tin_pos HJ W mem p n Hin Hnl b0 pl' Hpl Hin2 Hrq Hp4096 Hpc Hceilv Happ :=
  let HJb := fresh "HJb" in
  pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HJb & _);
  lazymatch goal with |- e01_in _ ?hx _ _ _ _ => apply (e01_in_cons hx _ _ _ _ p n Hin) end; cbn [e_src e_left e_len];
  [ reflexivity | reflexivity | exact Hnl | reflexivity
  | apply (e01_garr8_keep (w_H W) (w_H W) mem _);
    [ exact (e01_garr8_tl (mrestrict (w_H W) mem) p (bv_unsigned b0) (map (fun x : byte => bv_unsigned x) pl') Hpl)
    | let j := fresh "j" in let Hj := fresh "Hj" in intros j Hj; rewrite <- Z.add_assoc;
      apply (HJb p n (1 + Z.of_nat j) Hin Hin2); [| apply inFP_nil];
      rewrite length_map in Hj; cbn [length] in Hnl; revert Hj Hnl Hrq; clear; intros; lia ]
  | revert Hp4096; clear; lia
  | revert Hpc Hrq Hceilv; clear; intros; lia
  | revert Happ Hrq Hceilv; clear; intros;
    unfold amem_range, in_app, kLowShadowBeg, kHighMemBeg, kLowMemEnd, kHighMemEnd, ASAN_CEIL in *; lia ].

(* the write windows of P2's regions: the real-frame slots (the stack window), the frame's header and its shadow
   (the frame the journal owns) *)
Ltac e01_awr2 R S0 F pos U9 U10 U33 HRr HSTK HASTK :=
  lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
  let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0 fp b0 bc ly own) end;
  repeat first
  [ apply awr_ok_nil
  | apply awr_ok_cons_ro; [cbn; clear; lia|]
  | eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (R - S0));
    [reflexivity | rewrite U9; clear; lia
    | cbn; revert HRr HSTK HASTK; clear; intros; rewrite HASTK in HSTK; lia | cbn; revert HRr; clear; lia |]
  | eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 10%nat F); [reflexivity | exact U10 | |];
    [ cbn [YP09.r_wlo YP09.r_whi]; let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
      right; right; right; exists 3, pos; split; [left; reflexivity|];
      left; unfold in_zr; cbn [fst snd]; fold F; change (fs_frame_bytes 3) with 512; revert Ha; clear; lia |]
  | eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 33%nat (shadow_addr F)); [reflexivity | exact U33 | |];
    [ cbn [YP09.r_wlo YP09.r_whi]; let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
      right; right; right; exists 3, pos; split; [left; reflexivity|];
      right; unfold in_zr; cbn [fst snd]; fold F; change (fs_frame_bytes 3 / 8) with 64; revert Ha; clear; lia |] ].
Theorem e01_ok : rh_S_E01_stmt rsegs B RLO RHI RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK.
Proof.
intros hx HB.
destruct hx as [ly S W regs mem md p n pl].
unfold rh_base in HB. cbn [h_ly h_S h_W h_regs h_mem h_md h_p h_n h_pl] in HB.
pose proof HB as (HPRE & Hra & Hp & Hn & Hpn & Hnl & Hpl & Hfr0 & Hev & Hlive & HROD).
cbn [h_ly h_S h_W h_regs h_mem h_md h_p h_n h_pl].
pose proof HPRE as (HAR & Hra1 & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (AR_laws_ok rsegs B) as LAWS.
pose proof RPgCfgChanges.cfg_wx as Hwx. pose proof RPgCfgChanges.cfg_segs_low as Hsegs.
pose proof (ajournal_init rsegs B LLVMF_STK [] ly S W regs mem md [] HPRE) as HJ.
assert (HASTK : ASTACK = 16384) by reflexivity.
assert (Hpres1 : forall a, spZ regs - 0x1b0 <= a < spZ regs -> apresent (w_H W) mem a).
{ intros a Ha. apply Hpres. revert Ha HSTK HASTK. clear. intros. rewrite HASTK in HSTK. lia. }
assert (Hsp46 : 2 ^ 46 <= spZ regs <= 2 ^ 47).
{ revert C1 Hceil Hslo Hstk0 Hshi H47. clear. unfold ASTACK. intros. lia. }
pose proof (e01_p1a_entry W regs mem Hpres1 Hsp46 Hal16) as HS.
unfold cfg_at. change (w64 RH_ENTRY) with (Z_to_bv 64 E01_A).
aj_run_to E01_TBL_ok HS HJ 0x7ffcc.
{ lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
  let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0 fp b0 bc ly own) end.
  eapply awr_ok_cons_stack; [reflexivity | rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity
  | cbn; revert HSTK HASTK; clear; intros; rewrite HASTK in HSTK; lia | cbn; lia | apply awr_ok_nil]. }
(* ---- P1a's end, pc 0x7ffcc: sp = R, s0 = S, every other register as at the entry, the 13 saves ---- *)
set (R := 32 * ((spZ regs - 0x1a0) / 32)).
destruct (e01_R_range (spZ regs) Hal16 ltac:(revert Hsp46; clear; lia)) as (HRr & HR32 & HR16). fold R in HRr, HR32, HR16.
rename ms into ms1, HS into HS1, HJ into HJ1, HF into HF1, HFr into HFr1, HG into HG1.
rreg HS1 (2%bv : bv 5) R2.
assert (R2' : getr (ms_regs ms1) 2 = w64 R).
{ rewrite R2. unfold w64, R. apply e01_denot_and_m32.
  - rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl). symmetry. apply Z_to_bv_bv_unsigned.
  - revert Hsp46; clear; lia. - revert Hsp46; clear; lia. - revert Hsp46; clear; lia. }
clear R2.
assert (Hsp1 : spZ (ms_regs ms1) = R).
{ unfold spZ. rewrite R2'. unfold w64. apply unsigned_lit_small. revert Hsp46 HRr; clear; lia. }
destruct (al_const _ _ LAWS _ _ _ _ _ (proj1 HJ1)) as (Kc & Ku & Kg & Kgu).
rewrite HSC in Kc. rewrite HUC in Ku. rewrite HGOT, HSC in Kg. rewrite HGU, HUC in Kgu.
pose proof (RPgSteps.regs_kept_of_st_ok rsegs _ _ ms1 regs [] (w_H W) [2%bv; 8%bv] HS1 (env_agree_refl 32 _)
  ltac:(vm_compute; reflexivity)) as KR1.
assert (R8 : getr (ms_regs ms1) 8 = getr regs 2)
  by (rewrite (e01_reg_atom (w_H W) _ _ ms1 regs [] 8%bv 2 HS1 eq_refl ltac:(vm_compute; reflexivity) ltac:(lia)); reflexivity).
assert (SAV1 : forall j, (j < 13)%nat -> val_mem rsegs (mrestrict (w_H W) (ms_mem ms1))
  (spZ regs + (-8 - 8 * Z.of_nat j)) 8 (bv_unsigned (getr regs (nth j rh_saved_regs 0%bv)))).
{ lazymatch type of HS1 with st_ok _ _ ?ss _ =>
  let r := eval vm_compute in (nth_error (ss_mem ss) 0) in
  lazymatch r with Some ?rg =>
  apply (e01_saves_of_region _ (mrestrict (w_H W) (ms_mem ms1)) regs _ _ _ _ _
    (RPgCheckStr.st_ok_region_nth (w_H W) _ _ ms1 0 rg HS1 ltac:(vm_compute; reflexivity)) eq_refl);
  vm_compute; reflexivity end end. }
pose proof HJ1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJpres1 & _).
rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ ms1 HS1 eq_refl). cbn [ss_pc].
change (Z_to_bv 64 524236) with (Z_to_bv 64 E01_P1B).
pose proof (e01_p1b_entry W (ms_regs ms1) (ms_mem ms1)
  ltac:(intros a Ha; apply HJpres1; rewrite Hsp1 in Ha; revert Ha HRr HSTK HASTK; clear; intros; rewrite HASTK in HSTK; lia)
  ltac:(rewrite Hsp1; revert Hsp46 HRr; clear; lia) ltac:(rewrite Hsp1; exact HR32) Kgu Kg Ku Kc) as HS.
clear Kc Ku Kg Kgu.
(* ---- P1b: 0x7ffcc .. the `jal` 0x7fff8 to __asan_stack_malloc_3 ---- *)
aj_run_to E01_TBL_ok HS HJ1 E01_SM3.
{ lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
  let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0 fp b0 bc ly own) end.
  eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (R - spZ regs));
  [reflexivity | rewrite (ew_Ereg_nat (ms_regs ms1) _ 2 2%bv eq_refl); fold (spZ (ms_regs ms1)); rewrite Hsp1; lia
  | cbn; revert HRr HSTK HASTK; clear; intros; rewrite HASTK in HSTK; lia | cbn; revert HRr; clear; lia |].
  repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
(* ---- P1b's end, pc 0x3cbfc: ra = 0x7fffc, s1 = sp = R, s2 = n, s7 = K, R+0xc8 = p ---- *)
rename ms into ms2, HS into HS2, HF into HF2, HFr into HFr2, HG into HG2.
pose proof (RPgSteps.regs_kept_of_st_ok rsegs _ _ ms2 (ms_regs ms1) [] (w_H W) [1%bv; 9%bv; 10%bv; 11%bv; 12%bv; 18%bv; 23%bv]
  HS2 (env_agree_refl 32 _) ltac:(vm_compute; reflexivity)) as KR2.
assert (R2b : getr (ms_regs ms2) 2 = getr (ms_regs ms1) 2)
  by (rewrite (e01_reg_atom (w_H W) _ _ ms2 (ms_regs ms1) [] 2%bv 2 HS2 eq_refl ltac:(vm_compute; reflexivity) ltac:(lia)); reflexivity).
assert (R9b : getr (ms_regs ms2) 9 = getr (ms_regs ms1) 2)
  by (rewrite (e01_reg_atom (w_H W) _ _ ms2 (ms_regs ms1) [] 9%bv 2 HS2 eq_refl ltac:(vm_compute; reflexivity) ltac:(lia)); reflexivity).
assert (R18b : getr (ms_regs ms2) 18 = getr (ms_regs ms1) 11)
  by (rewrite (e01_reg_atom (w_H W) _ _ ms2 (ms_regs ms1) [] 18%bv 11 HS2 eq_refl ltac:(vm_compute; reflexivity) ltac:(lia)); reflexivity).
assert (R1b : getr (ms_regs ms2) 1 = Z_to_bv 64 E01_SM3_RA)
  by exact (e01_reg_lit (w_H W) _ _ ms2 1%bv _ HS2 ltac:(vm_compute; reflexivity)).
assert (R23b : getr (ms_regs ms2) 23 = Z_to_bv 64 SHADOW_OFF)
  by exact (e01_reg_lit (w_H W) _ _ ms2 23%bv _ HS2 ltac:(vm_compute; reflexivity)).
assert (Hsp2 : spZ (ms_regs ms2) = R) by (unfold spZ; rewrite R2b; exact Hsp1).
assert (SMP : stack_malloc_progressP B) by (intros s cid H1 H2 H3; exact (ml_stack_malloc_progress _ ML s cid H1 H2 H3)).
pose proof (YM05.alloc_ceiling_val) as Hceilv.
assert (Hn26 : 0 <= n < 2 ^ 26) by (revert Hpn; clear; intros [[-> _] | [Hn' _]]; lia).
assert (Hp64 : 0 <= p < 2 ^ 64).
{ destruct Hpn as [[_ ->] | [_ Hin]].
  - revert HAE C5; clear; unfold kLowMemEnd; lia.
  - destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR Hin) as (_ & H4 & Hc & _). pose proof (req_size_pos n ltac:(lia)) as Hrq.
    revert H4 Hc Hceilv Hrq; clear; intros; lia. }
assert (SLT2 : val_mem rsegs (mrestrict (w_H W) (ms_mem ms2)) (R + 0xc8) 8 p).
{ lazymatch type of HS2 with st_ok _ _ ?ss _ =>
  let r := eval vm_compute in (nth_error (ss_mem ss) 0) in
  lazymatch r with Some ?rg =>
  pose proof (RPgCheckStr.st_ok_region_nth (w_H W) _ _ ms2 0 rg HS2 ltac:(vm_compute; reflexivity)) as Hrg end end.
  change (R + 0xc8) with (R + 200).
  apply (RPgCheckStr.field_of_region _ _ 2 R _ _ _ _ _ 200 8 (SOff 10 0) p Hrg).
  - rewrite (ew_Ereg_nat (ms_regs ms1) _ 2 2%bv eq_refl). exact Hsp1.
  - cbn. left. reflexivity.
  - apply bv_eq. rewrite denot_SOff, Z.add_0_r, (ew_Ereg_nat (ms_regs ms1) _ 10 10%bv eq_refl).
    rewrite KR1 by (vm_compute; first [discriminate | intros [H|[H|[]]]; discriminate H]). rewrite Hp.
    unfold w64. rewrite !unsigned_lit_small by lia. apply zcanon_id. unfold M64. lia.
  - cbn. lia.
  - cbn. lia. }
rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ ms2 HS2 eq_refl). cbn [ss_pc].
replace 248828 with (pc_stack_malloc (as_code B) 3) by (rewrite HBsm; reflexivity).
eapply SRr_bind.
{ apply (aj_stack_malloc_at rsegs B LAWS Hsegs errno_low ML SMP 3 ASM3 ltac:(lia) W (ms_regs ms2) (ms_mem ms2)
    LLVMF_STK (spZ regs) [] ly S W mem md [] ly S _ 0 (R - spZ regs) (Z_to_bv 64 E01_SM3_RA) HJ1).
  - rewrite Hsp2. lia.
  - exact HR16.
  - revert HRr; clear; lia.
  - revert HRr HSTK HASTK; clear; intros; rewrite HASTK in HSTK; unfold ESTACK; lia.
  - rewrite KR2 by (vm_compute; first [discriminate | intros [H|[H|[H|[H|[H|[H|[H|[]]]]]]]]; discriminate H]).
    rewrite KR1 by (vm_compute; first [discriminate | intros [H|[H|[]]]; discriminate H]). exact Hgp.
  - rewrite KR2 by (vm_compute; first [discriminate | intros [H|[H|[H|[H|[H|[H|[H|[]]]]]]]]; discriminate H]).
    rewrite KR1 by (vm_compute; first [discriminate | intros [H|[H|[]]]; discriminate H]). exact Htp.
  - exact R1b.
  - vm_compute. reflexivity.
  - rewrite Hfr0. reflexivity. }
cbv beta. intros W2 c2 _ (-> & S2 & regs3 & mem3 & md3 & pos & -> & HJ3 & HP3 & Ha03 & Eab3 & Hfrs3 & Hnin3 & Hnev3 & Hbb3 & Hz3 & Hflag3 & HK3).
(* ---- the frame F and its facts, after the call ---- *)
assert (Hfin : In (3, pos) (frames S2)) by (rewrite Hfrs3; left; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ 3 pos (proj1 HJ3) Hfin) as (HF32 & HFapp & HFpres & HFSpres).
destruct (frames_bounds rsegs B LAWS _ _ _ _ _ 3 pos (proj1 HJ3) Hfin) as (HF4096 & HFceil & HFapp2).
change (fs_frame_bytes 3) with 512 in *. change (512 / 8) with 64 in HFSpres.
set (F := frame_addr ly 3 pos) in *.
pose proof HJ3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJpres3 & _).
assert (CS3 : forall r : bv 5, acallee_saved (bv_unsigned r) -> getr regs3 r = getr (ms_regs ms2) r).
{ intros r Hr. pose proof (HP3 (bv_unsigned r) Hr) as X. rewrite Z_to_bv_bv_unsigned in X. exact X. }
assert (Hcs : forall z, z = 9 \/ z = 18 \/ z = 23 -> acallee_saved z) by (unfold acallee_saved; clear; intros; lia).
assert (R9c : getr regs3 9 = w64 R).
{ rewrite CS3 by (apply Hcs; left; reflexivity). rewrite R9b. exact R2'. }
assert (R18c : getr regs3 18 = w64 n).
{ rewrite CS3 by (apply Hcs; right; left; reflexivity). rewrite R18b.
  rewrite KR1 by (vm_compute; first [discriminate | intros [H|[H|[]]]; discriminate H]). exact Hn. }
assert (R23c : getr regs3 23 = w64 SHADOW_OFF).
{ rewrite CS3 by (apply Hcs; right; right; reflexivity). exact R23b. }
assert (SLT3 : val_mem rsegs (mrestrict (w_H W) mem3) (R + 0xc8) 8 p).
{ apply (val_mem_kept rsegs (w_H W) (w_H W) (ms_mem ms2) mem3); [|exact SLT2].
  intros k Hk. pose proof HK3 as (K1 & _). apply K1.
  - revert Hk HRr Hceil Hslo Hstk0 Hshi H47 HSTK HASTK. clear. intros. rewrite HASTK in HSTK. cbn in Hk. lia.
  - revert Hk HRr. clear. intros. unfold ESTACK. cbn in Hk. lia. }
set (sv0 := match aview rsegs (w_H W) mem3 (shadow_of_addr SHADOW_OFF p) with Some v => v | None => 0 end).
set (bv0 := match aview rsegs (w_H W) mem3 p with Some v => v | None => 0 end).
assert (HF8 : F = 8 * (F / 8) + F mod 8 /\ 0 <= F mod 8 < 8) by (split; [apply Z.div_mod; lia | apply Z.mod_pos_bound; lia]).
assert (HDJ : zpairwise_disjoint [(R + 0x30, R + 0x118); (F, F + 24); (shadow_addr F, shadow_addr F + 52)]).
{ cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj, shadow_addr, SHADOW_OFF. cbn [fst snd].
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp.
  revert HF8 HFapp HFceil Hceilv HRr Hceil Hslo Hstk0 HSTK HASTK. clear. intros. rewrite HASTK in HSTK.
  repeat split; lia. }
pose proof (e01_p2_entry W regs3 mem3 R F n p sv0 bv0 R9c Ha03 R18c
  ltac:(revert HRr Hsp46; clear; lia) ltac:(revert HRr Hsp46; clear; lia)
  ltac:(exact HF4096) ltac:(revert HFceil Hceilv; clear; lia) HF32 Hn26 Hp64
  ltac:(intros a Ha; apply HJpres3; revert Ha HRr HSTK HASTK; clear; intros; rewrite HASTK in HSTK; lia)
  ltac:(intros a Ha; apply (proj1 (HFpres a ltac:(revert Ha; clear; lia))))
  ltac:(intros i Hi; apply (proj1 (HFSpres i ltac:(revert Hi; clear; lia))))
  SLT3 HDJ) as HS.
clear HDJ.
(* the alias of the frame's shadow base (F >> 3) + K *)
lazymatch type of HS with st_ok _ ?Ev _ _ =>
  pose proof (st_ok_add_alias rsegs Ev _ _ (SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 0) (SLit 3)) (SOff 23 0)) (SOff 33 0) HS
    (shadow_decl_ok Ev 10 23 33 F SHADOW_OFF
      ltac:(rewrite (ew_Ereg_nat regs3 _ 10 10%bv eq_refl); exact Ha03) ltac:(revert HF4096 HFceil Hceilv; clear; lia)
      ltac:(rewrite (ew_Ereg_nat regs3 _ 23 23%bv eq_refl); exact R23c)
      ltac:(rewrite (ew_Ereg_extra regs3 _ 1); reflexivity))) as HS4 end.
clear HS. rename HS4 into HS.
assert (HshF3 : 0 <= shadow_addr F < 2 ^ 45).
{ revert HF4096 HFceil Hceilv. clear. intros. unfold shadow_addr, SHADOW_OFF.
  split; [apply Z.add_nonneg_nonneg; [lia | apply Z.div_pos; lia]|].
  assert (F / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; lia). lia. }
assert (U9 : bv_unsigned (ew (Ereg regs3 (e01_p2_extra p F sv0 bv0)) 9) = R).
{ rewrite (ew_Ereg_nat regs3 _ 9 9%bv eq_refl), R9c. unfold w64. apply unsigned_lit_small. revert HRr Hsp46; clear; lia. }
assert (U10 : bv_unsigned (ew (Ereg regs3 (e01_p2_extra p F sv0 bv0)) 10) = F).
{ rewrite (ew_Ereg_nat regs3 _ 10 10%bv eq_refl), Ha03. unfold w64. apply unsigned_lit_small. revert HF4096 HFceil Hceilv; clear; lia. }
assert (U33 : bv_unsigned (ew (Ereg regs3 (e01_p2_extra p F sv0 bv0)) 33) = shadow_addr F).
{ rewrite (ew_Ereg_extra regs3 _ 1). cbn [nth e01_p2_extra]. unfold w64. apply unsigned_lit_small. revert HshF3; clear; lia. }
(* ---- what P2 keeps: the 13 saves (P1a's, through P1b and the frame call) and the flag pointer word ---- *)
assert (K12 : forall a, 0 <= a < 2 ^ 64 -> ~ (R + 0xc8 <= a < R + 0xd0) ->
  aview rsegs (w_H W) (ms_mem ms2) a = aview rsegs (w_H W) (ms_mem ms1) a).
{ lazymatch type of HFr2 with frame_of ?E ?rs (mrestrict ?H ?m0) (mrestrict _ ?m1) =>
  apply (e01_keep_frame E rs H m0 m1 _ HFr2) end.
  let a := fresh "a" in let r := fresh "r" in let Hin := fresh "Hin" in let Ha := fresh "Ha" in
  intros a (r & Hin & Ha);
  lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end;
  repeat (destruct Hin as [<- | Hin];
    [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
      first [ rewrite (ew_Ereg_nat (ms_regs ms1) _ 2 2%bv eq_refl) in Ha; fold (spZ (ms_regs ms1)) in Ha;
              rewrite Hsp1 in Ha; lia | lia ] | ]); destruct Hin. }
assert (SAV3 : forall j, (j < 13)%nat -> val_mem rsegs (mrestrict (w_H W) mem3)
  (spZ regs + (-8 - 8 * Z.of_nat j)) 8 (bv_unsigned (getr regs (nth j rh_saved_regs 0%bv)))).
{ intros j Hj. apply (e01_val_mem_keep (w_H W) (ms_mem ms1) mem3); [|exact (SAV1 j Hj)].
  intros k Hk. cbn in Hk. pose proof HK3 as (K1 & _).
  assert (Hjz : 0 <= Z.of_nat j <= 12) by lia.
  assert (Hbd : alloc_ceiling <= spZ regs - 0x68 /\ spZ regs <= 2 ^ 47).
  { revert Hceil Hslo Hshi H47 HSTK HASTK; clear; intros; rewrite HASTK in HSTK; lia. }
  rewrite K1.
  - apply K12.
    + revert Hjz Hk Hbd Hceilv; clear; intros; lia.
    + revert Hjz Hk Hbd HRr; clear; intros; lia.
  - revert Hjz Hk Hbd; clear; intros; lia.
  - revert Hjz Hk Hbd HRr; clear; intros; unfold ESTACK; lia. }
assert (FLG3 : val_mem rsegs (mrestrict (w_H W) mem3) (F + 0x1f8) 8 (flag_addr ly 3 pos)).
{ replace (F + 0x1f8) with (F + 512 - 8) by lia. exact (val_mem_of_rdword rsegs (w_H W) mem3 _ _ Hflag3). }
assert (KP2 : forall a, 0 <= a < 2 ^ 64 -> ~ e01_p2win R F a -> aview rsegs (w_H W) mem3 a = aview rsegs (w_H W) mem3 a)
  by reflexivity.
(* ---- the values K80194's cut reads, from the entry through P1a, P1b and the frame call ---- *)
assert (Hcs' : forall z, z = 2 \/ z = 3 \/ z = 4 \/ z = 8 -> acallee_saved z) by (unfold acallee_saved; clear; intros; lia).
assert (G2 : getr regs3 2 = w64 R).
{ rewrite CS3 by (apply Hcs'; left; reflexivity). rewrite R2b. exact R2'. }
assert (G3 : getr regs3 3 = w64 (as_gp B)).
{ rewrite CS3 by (apply Hcs'; right; left; reflexivity).
  rewrite KR2 by (vm_compute; first [discriminate | intros [H|[H|[H|[H|[H|[H|[H|[]]]]]]]]; discriminate H]).
  rewrite KR1 by (vm_compute; first [discriminate | intros [H|[H|[]]]; discriminate H]). exact Hgp. }
assert (G4 : getr regs3 4 = w64 (as_tp B)).
{ rewrite CS3 by (apply Hcs'; right; right; left; reflexivity).
  rewrite KR2 by (vm_compute; first [discriminate | intros [H|[H|[H|[H|[H|[H|[H|[]]]]]]]]; discriminate H]).
  rewrite KR1 by (vm_compute; first [discriminate | intros [H|[H|[]]]; discriminate H]). exact Htp. }
assert (G8 : getr regs3 8 = w64 (spZ regs)).
{ rewrite CS3 by (apply Hcs'; right; right; right; reflexivity).
  rewrite KR2 by (vm_compute; first [discriminate | intros [H|[H|[H|[H|[H|[H|[H|[]]]]]]]]; discriminate H]).
  rewrite R8. unfold w64, spZ. symmetry. apply Z_to_bv_bv_unsigned. }
assert (U18 : bv_unsigned (ew (Ereg regs3 (e01_p2_extra p F sv0 bv0)) 18) = n).
{ rewrite (ew_Ereg_nat regs3 _ 18 18%bv eq_refl), R18c. unfold w64. apply unsigned_lit_small. revert Hn26; clear; lia. }
assert (U32 : bv_unsigned (ew (Ereg regs3 (e01_p2_extra p F sv0 bv0)) 32) = p).
{ rewrite (ew_Ereg_extra regs3 _ 0). cbn [nth e01_p2_extra]. unfold w64. apply unsigned_lit_small. exact Hp64. }
(* the saves and the flag pointer word lie outside P2's windows *)
assert (HF8z : F mod 8 = 0).
{ revert HF32. clear. intros. pose proof (Z.div_mod F 32 ltac:(lia)) as D. rewrite HF32, Z.add_0_r in D.
  rewrite D. replace (32 * (F / 32)) with ((4 * (F / 32)) * 8) by lia. apply Z_mod_mult. }
assert (NWsav : forall j k, (j < 13)%nat -> 0 <= k < 8 ->
  0 <= spZ regs + (-8 - 8 * Z.of_nat j) + k < 2 ^ 64 /\ ~ e01_p2win R F (spZ regs + (-8 - 8 * Z.of_nat j) + k)).
{ intros j k Hj Hk. assert (Hjz : 0 <= Z.of_nat j <= 12) by lia.
  unfold e01_p2win. unfold shadow_addr, SHADOW_OFF in HshF3 |- *.
  revert Hjz Hk HRr Hceil Hslo Hshi H47 HSTK HASTK Hceilv HFceil HshF3. clear. intros. rewrite HASTK in HSTK. lia. }
assert (NWflg : forall k, 0 <= k < 8 -> 0 <= F + 0x1f8 + k < 2 ^ 64 /\ ~ e01_p2win R F (F + 0x1f8 + k)).
{ intros k Hk. pose proof (Z.div_mod F 8 ltac:(lia)) as DF. rewrite HF8z, Z.add_0_r in DF.
  unfold e01_p2win. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp. unfold shadow_addr, SHADOW_OFF.
  revert Hk DF HRr Hceil Hslo Hshi H47 HSTK HASTK Hceilv HFceil HFapp HF4096. clear. intros. rewrite HASTK in HSTK. lia. }
(* ---- P2: 0x7fffc .. 0x80140 `beqz a3` (a3 = n >> 26): `bnez s6` is taken (F >= 4096), the header, the 52
   shadow stores ---- *)
aj_run E01_TBL_ok HS HJ3. { e01_awr2 R (spZ regs) F pos U9 U10 U33 HRr HSTK HASTK. }
e01_keep2 HFr KP2 R F U9 U10 U33.
rename ms into ms4, HS into HS4, HJ3 into HJ4, HF into HF4, HFr into HFr4, HG into HG4.
lazymatch goal with |- SRr _ ?Wg (mkCfg ?msF ?mdF) _ =>
  lazymatch type of HS4 with st_ok _ ?Ev ?ssv _ =>
  apply (SRr_sym_branch rsegs Wg Ev ssv msF mdF _ BC_EQ (SAlu ALU_SRL (SOff 18 0) (SLit 26)) (SLit 0) HS4) end end;
intros Hc HS5; clear HS4.
2:{ (* not taken: n >> 26 <> 0, impossible *)
  exfalso. rewrite branch_eq_U, U_SAlu in Hc. cbn [zalu_raw] in Hc.
  rewrite (U_atom _ 18 n) in Hc; [| rewrite (ew_Ereg_nat regs3 _ 18 18%bv eq_refl); exact R18c | revert Hn26; clear; lia].
  rewrite !U_SLit in Hc. change (Z.land (zcanon 26) 63) with 26 in Hc. change (zcanon 0) with 0 in Hc.
  rewrite Z.shiftr_div_pow2 in Hc by lia. rewrite (Z.div_small n (2 ^ 26)) in Hc by (revert Hn26; clear; lia).
  vm_compute in Hc. discriminate Hc. }
(* taken: 0x80148 `beqz s2` (s2 = n) *)
aj_run E01_TBL_ok HS5 HJ4. { e01_awr2 R (spZ regs) F pos U9 U10 U33 HRr HSTK HASTK. }
e01_keep2 HFr KP2 R F U9 U10 U33.
rename ms into ms5, HS5 into HS6, HJ4 into HJ6, HF into HF6, HFr into HFr6, HG into HG6.
lazymatch goal with |- SRr _ ?Wg (mkCfg ?msF ?mdF) _ =>
  lazymatch type of HS6 with st_ok _ ?Ev ?ssv _ =>
  apply (SRr_sym_branch rsegs Wg Ev ssv msF mdF _ BC_EQ (SOff 18 0) (SLit 0) HS6) end end;
intros Hc2 HS7; clear HS6.
- (* taken: n = 0, the flags byte is 0 and nothing is left *)
  assert (Hn0 : n = 0).
  { rewrite branch_eq_U in Hc2. rewrite (U_atom _ 18 n) in Hc2;
    [| rewrite (ew_Ereg_nat regs3 _ 18 18%bv eq_refl); exact R18c | revert Hn26; clear; lia].
    rewrite U_SLit in Hc2. change (zcanon 0) with 0 in Hc2. apply Z.eqb_eq in Hc2. exact Hc2. }
  aj_run_to E01_TBL_ok HS7 HJ6 E01_MALLOC. { e01_awr2 R (spZ regs) F pos U9 U10 U33 HRr HSTK HASTK. }
  e01_keep2 HFr KP2 R F U9 U10 U33.
  assert (Hpa : p = A_EMPTY).
  { destruct Hpn as [[_ Hpa] | [Hx _]]; [exact Hpa | exfalso; rewrite Hn0 in Hx; revert Hx; clear; lia]. }
  e01_fin HS7 HJ6 KP2 (RLEnv (spZ regs) R F 0 0 (rl_len []) 0 p 0) (@nil byte) W F mem3 HB Eab3 U33 SAV3 NWsav FLG3 NWflg;
  [ cbn [e_fl]; split; [apply Z.le_refl | reflexivity]
  | apply e01_in_nil; cbn [e_left e_len e_src];
    [reflexivity | reflexivity | rewrite Hpa; exact (proj1 HAE) | rewrite Hpa; exact (proj2 HAE)] ].
- (* not taken: n > 0: the flags byte data[0] behind its shadow check *)
  assert (Hn0 : n <> 0).
  { intros Hz. rewrite branch_eq_U in Hc2. rewrite (U_atom _ 18 n) in Hc2;
    [| rewrite (ew_Ereg_nat regs3 _ 18 18%bv eq_refl); exact R18c | revert Hn26; clear; lia].
    rewrite U_SLit in Hc2. change (zcanon 0) with 0 in Hc2. rewrite Hz in Hc2. vm_compute in Hc2. discriminate Hc2. }
  clear Hc2.
  assert (Hnp : 0 < n < 2 ^ 26 /\ In (p, n) (ablocks B ly S)).
  { destruct Hpn as [[Hz _] | Hx]; [contradiction | exact Hx]. }
  destruct Hnp as [Hnr Hin].
  assert (Hin2 : In (p, n) (ablocks B ly S2)) by (rewrite Eab3; exact Hin).
  lazymatch type of HS7 with st_ok _ _ _ (restrict _ ?msx) => set (m7 := ms_mem msx) end.
  pose proof (proj1 HJ6) as HAR7.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR7 Hin2) as (Hp16 & Hp4096 & Hpc & Happ & _).
  pose proof (req_size_pos n ltac:(lia)) as Hrq.
  pose proof (sep_block_frame rsegs B LAWS ly S2 W _ _ p n 3 pos HAR7 Hin2 Hfin) as HdPF.
  unfold zdisjoint in HdPF. cbn [fst snd] in HdPF. change (fs_frame_bytes 3) with 512 in HdPF. fold F in HdPF.
  assert (Hp8 : p mod 8 = 0).
  { revert Hp16. clear. intros. pose proof (Z.div_mod p 16 ltac:(lia)). rewrite Hp16, Z.add_0_r in H.
    rewrite H, Z.mul_comm. replace (p / 16 * 16) with ((p / 16 * 2) * 8) by lia. apply Z_mod_mult. }
  (* the shadow cell of p and the byte at p lie outside P2's windows *)
  assert (HshP : SHADOW_OFF <= shadow_of_addr SHADOW_OFF p < kHighMemBeg).
  { revert Hp4096 Hpc Hceilv Hrq. clear. intros. unfold shadow_of_addr, kHighMemBeg.
    assert (0 <= p / 8) by (apply Z.div_pos; lia).
    assert (p / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia). unfold SHADOW_OFF in *. lia. }
  assert (NWs : ~ e01_p2win R F (shadow_of_addr SHADOW_OFF p)).
  { unfold e01_p2win. intros [Hx | [Hx | Hx]].
    - revert Hx HshP HRr Hceil Hslo Hceilv HSTK HASTK. clear. intros. rewrite HASTK in HSTK.
      unfold kHighMemBeg in HshP. lia.
    - unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp. unfold kHighMemBeg in HshP.
      unfold SHADOW_OFF in HshP, Hx. revert Hx HFapp HshP. clear. intros. lia.
    - unfold shadow_of_addr, shadow_addr in Hx. 
      pose proof (Z.div_mod p 8 ltac:(lia)) as Dp. pose proof (Z.div_mod F 8 ltac:(lia)) as DF.
      rewrite Hp8 in Dp. destruct HF8 as [_ HF8b].
      rewrite HF8z in DF. revert Hx Dp DF HdPF Hrq. clear. intros. lia. }
  assert (NWp : ~ e01_p2win R F p).
  { unfold e01_p2win. intros [Hx | [Hx | Hx]].
    - revert Hx Hpc Hrq HRr Hceil Hslo HSTK HASTK. clear. intros. rewrite HASTK in HSTK. lia.
    - revert Hx HdPF Hrq. clear. intros. lia.
    - apply (e01m_sh_app F (p - shadow_addr F) p (req_size n) HF4096 HFceil); [revert Hx; clear; lia | exact Happ |].
      revert Hrq. clear. intros. lia. }
  (* the shadow byte s of p (n in 1 .. 7 at the last, partial granule: s = n) and the byte data[0] *)
  destruct (RPgMem.rm_A_80158_cell rsegs B ly S2 W _ _ p n HAR7 Hin2 ltac:(lia)) as (s & Hs & Hsok & Hsslow).
  assert (Hs8 : 0 <= s < 8) by (revert Hsok Hsslow Hp8; clear; unfold saddr_ok; intros; lia).
  assert (Esv : sv0 = s).
  { subst sv0. rewrite <- (KP2 (shadow_of_addr SHADOW_OFF p) ltac:(revert HshP; clear; unfold kHighMemBeg, SHADOW_OFF; lia) NWs).
    rewrite Hs. reflexivity. }
  destruct pl as [|b0 pl']; [cbn in Hnl; exfalso; exact (Hn0 Hnl)|].
  assert (Hb0 : aview rsegs (w_H W) mem p = Some (bv_unsigned b0)).
  { destruct (Hpl 0%nat ltac:(cbn; apply Nat.lt_0_succ)) as (V & _). cbn [nth map] in V.
    pose proof (V 0%nat ltac:(apply Nat.lt_0_1)) as V0. rewrite !Z.add_0_r in V0. unfold aview. rewrite V0. cbn [option_map].
    f_equal. rewrite Z_to_bv_unsigned. unfold YO0f.le_byte.
    change (8 * Z.of_nat 0) with 0. change (8 * Z.of_nat 1) with 8. rewrite Z.shiftr_0_r.
    pose proof (bv_unsigned_in_range 8 b0) as Rb. change (bv_modulus 8) with 256 in Rb.
    change (2 ^ 8) with 256. rewrite !(Z.mod_small (bv_unsigned b0) 256) by exact Rb. apply bv_wrap_small. exact Rb. }
  pose proof HJ6 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HJblk6 & _).
  assert (Hb7 : aview rsegs (w_H W) m7 p = Some (bv_unsigned b0)).
  { pose proof (HJblk6 p n 0 Hin Hin2 ltac:(revert Hrq; clear; lia) (inFP_nil _)) as X. rewrite !Z.add_0_r in X. exact (eq_trans X Hb0). }
  assert (Ebv : bv0 = bv_unsigned b0).
  { subst bv0. rewrite <- (KP2 _ Hp64 NWp). unfold m7 in Hb7. rewrite Hb7. reflexivity. }
  (* the engine's view of the check: atoms 35 (s) and 36 (data[0]) bounded, the alias (p >> 3) + K = atom 34,
     and two one-byte read-only regions: the shadow cell at atom 34 and the byte at atom 32 *)
  assert (U34 : bv_unsigned (ew (Ereg regs3 (e01_p2_extra p F sv0 bv0)) 34) = shadow_of_addr SHADOW_OFF p).
  { rewrite (ew_Ereg_extra regs3 _ 2). cbn [nth e01_p2_extra]. unfold w64. apply unsigned_lit_small.
    revert HshP; clear; unfold kHighMemBeg, SHADOW_OFF; lia. }
  assert (U35 : bv_unsigned (ew (Ereg regs3 (e01_p2_extra p F sv0 bv0)) 35) = s).
  { rewrite (ew_Ereg_extra regs3 _ 3). cbn [nth e01_p2_extra]. unfold w64. rewrite Esv. apply unsigned_lit_small.
    revert Hs8; clear; lia. }
  assert (U36 : bv_unsigned (ew (Ereg regs3 (e01_p2_extra p F sv0 bv0)) 36) = bv_unsigned b0).
  { rewrite (ew_Ereg_extra regs3 _ 4). cbn [nth e01_p2_extra]. unfold w64. rewrite Ebv. apply unsigned_lit_small.
    pose proof (bv_unsigned_in_range 8 b0) as Rb. change (bv_modulus 8) with 256 in Rb. revert Rb; clear; lia. }
  pose proof (bv_unsigned_in_range 8 b0) as Rb0. change (bv_modulus 8) with 256 in Rb0.
  lazymatch type of HS7 with st_ok _ ?Ev ?ssv ?msv =>
    pose proof (st_ok_add_fact rsegs Ev ssv msv 35 (mkAF 0 7 0) HS7
      ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U35, Z.pow_0_r, Z.mod_1_r; revert Hs8; clear; lia)) as HS8 end.
  clear HS7.
  lazymatch type of HS8 with st_ok _ ?Ev ?ssv ?msv =>
    pose proof (st_ok_add_fact rsegs Ev ssv msv 36 (mkAF 0 255 0) HS8
      ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U36, Z.pow_0_r, Z.mod_1_r; revert Rb0; clear; lia)) as HS9 end.
  clear HS8.
  lazymatch type of HS9 with st_ok _ ?Ev ?ssv ?msv =>
    pose proof (st_ok_add_alias rsegs Ev ssv msv (SAlu ALU_ADD (SAlu ALU_SRL (SOff 32 0) (SLit 3)) (SOff 23 0)) (SOff 34 0) HS9
      (shadow_decl_ok Ev 32 23 34 p SHADOW_OFF
        ltac:(rewrite (ew_Ereg_extra regs3 _ 0); reflexivity) Hp64
        ltac:(rewrite (ew_Ereg_nat regs3 _ 23 23%bv eq_refl); exact R23c)
        ltac:(rewrite (ew_Ereg_extra regs3 _ 2); reflexivity))) as HS10 end.
  clear HS9.
  assert (Hs7 : aview rsegs (w_H W) m7 (shadow_of_addr SHADOW_OFF p) = Some s) by exact Hs.
  lazymatch type of HS10 with st_ok _ ?Ev ?ssv (restrict ?Hh ?msv) =>
    pose proof (RPgMem.rm_cell_region rsegs Ev (w_H W) m7 34 (shadow_of_addr SHADOW_OFF p) s (SOff 35 0) U34 Hs7
      ltac:(apply bv_eq; rewrite denot_SOff, Z.add_0_r, U35; rewrite unsigned_lit_small by (revert Hs8; clear; lia);
            apply zcanon_id; unfold M64; revert Hs8; clear; lia)
      ltac:(revert HshP; clear; unfold kHighMemBeg, SHADOW_OFF; lia)
      ltac:(revert HshP; clear; unfold kHighMemBeg, SHADOW_OFF; lia)) as RGs;
    pose proof (RPgMem.rm_cell_region rsegs Ev (w_H W) m7 32 p (bv_unsigned b0) (SOff 36 0) U32 Hb7
      ltac:(apply bv_eq; rewrite denot_SOff, Z.add_0_r, U36; rewrite unsigned_lit_small by (revert Rb0; clear; lia);
            apply zcanon_id; unfold M64; revert Rb0; clear; lia)
      ltac:(revert Hp64; clear; lia) ltac:(revert Hp64; clear; lia)) as RGp end.
  lazymatch type of HS10 with st_ok ?sg ?Ev ?ssx ?msx =>
    let ss' := eval vm_compute in ssx in
    let Ess := fresh "Ess" in
    assert (Ess : ssx = ss') by (vm_compute; reflexivity); rewrite Ess in HS10; clear Ess end.
  Ltac e01_dj NWs NWp HshP Happ Hrq :=
    revert NWs NWp HshP Happ Hrq; clear; intros;
    unfold e01_p2win, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF in *; lia.
  Ltac e01_djgoal U9 U10 U33 U34 U32 NWs NWp HshP Happ Hrq :=
    apply all_disjoint_of_extents; unfold extent_of_region;
    cbn [map ss_mem YP09.r_base YP09.r_lo YP09.r_hi base_val zall_disjoint]; rewrite ?U9, ?U10, ?U33, ?U34, ?U32;
    unfold zdisj; cbn [fst snd]; repeat split; e01_dj NWs NWp HshP Happ Hrq.
  lazymatch type of HS10 with st_ok _ ?Ev ?ssv ?msv =>
  lazymatch type of RGs with region_ok _ _ _ ?r1 =>
    assert (DJ1 : all_disjoint Ev r1 (ss_mem ssv)) by (e01_djgoal U9 U10 U33 U34 U32 NWs NWp HshP Happ Hrq);
    pose proof (ast_ok_add_region rsegs Ev ssv msv r1 HS10 eq_refl RGs DJ1) as HS11 end end.
  clear HS10 DJ1.
  lazymatch type of HS11 with st_ok _ ?Ev ?ssv ?msv =>
  lazymatch type of RGp with region_ok _ _ _ ?r1 =>
    assert (DJ2 : all_disjoint Ev r1 (ss_mem ssv)) by (e01_djgoal U9 U10 U33 U34 U32 NWs NWp HshP Happ Hrq);
    pose proof (ast_ok_add_region rsegs Ev ssv msv r1 HS11 eq_refl RGp DJ2) as HS12 end end.
  clear HS11 DJ2 RGs RGp.
  lazymatch type of HS12 with st_ok ?sg ?Ev ?ssx ?msx =>
    let ss' := eval vm_compute in ssx in
    let Ess := fresh "Ess" in
    assert (Ess : ssx = ss') by (vm_compute; reflexivity); rewrite Ess in HS12; clear Ess end.
  (* 0x8014c .. the `beqz a0` 0x8015c of the check *)
  aj_run E01_TBL_ok HS12 HJ6. { e01_awr2 R (spZ regs) F pos U9 U10 U33 HRr HSTK HASTK. }
  e01_keep2 HFr KP2 R F U9 U10 U33.
  rename ms into ms8, HS12 into HS13, HJ6 into HJ8, HF into HF8x, HFr into HFr8, HG into HG8.
  lazymatch goal with |- SRr _ ?Wg (mkCfg ?msF ?mdF) _ =>
    lazymatch type of HS13 with st_ok _ ?Ev ?ssv _ =>
    apply (SRr_sym_branch rsegs Wg Ev ssv msF mdF _ BC_EQ (SOff 35 0) (SLit 0) HS13) end end;
  intros Hc3 HS14; clear HS13.
  + (* s = 0: the granule of p is whole; 0x80164 *)
    aj_run_to E01_TBL_ok HS14 HJ8 E01_MALLOC. { e01_awr2 R (spZ regs) F pos U9 U10 U33 HRr HSTK HASTK. }
    e01_keep2 HFr KP2 R F U9 U10 U33.
    e01_fin HS14 HJ8 KP2 (RLEnv (spZ regs) R F 0 0 (rl_len pl') (bv_unsigned b0) (p + 1) (n - 1)) pl' W F mem3 HB Eab3 U33 SAV3 NWsav FLG3 NWflg;
    [ cbn [e_fl]; exact Rb0 | e01_tin_pos HJ8 W mem p n Hin Hnl b0 pl' Hpl Hin2 Hrq Hp4096 Hpc Hceilv Happ ].
  + (* s <> 0 (n in 1 .. 7, s = n): the slow block 0x82610 *)
    aj_run E01_TBL_ok HS14 HJ8. { e01_awr2 R (spZ regs) F pos U9 U10 U33 HRr HSTK HASTK. }
    e01_keep2 HFr KP2 R F U9 U10 U33.
    assert (Hs0 : s <> 0).
    { intros Hz. rewrite branch_eq_U in Hc3. rewrite (U_atom _ 35 s) in Hc3;
      [| rewrite (ew_Ereg_extra regs3 _ 3); cbn [nth e01_p2_extra]; rewrite Esv; reflexivity | revert Hs8; clear; lia].
      rewrite U_SLit in Hc3. change (zcanon 0) with 0 in Hc3. rewrite Hz in Hc3. vm_compute in Hc3. discriminate Hc3. }
    clear Hc3.
    rename ms into ms9, HS14 into HS15, HJ8 into HJ9, HF into HF9, HFr into HFr9, HG into HG9.
    assert (D1 : sv_denot (Ereg regs3 (e01_p2_extra p F sv0 bv0)) (SAlu ALU_AND (SOff 32 0) (SLit 7)) = Z_to_bv 64 (p mod 8)).
    { rewrite denot_lit_U. f_equal. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit, (U_atom _ 32 p).
      - change (zcanon 7) with 7. assert (L7 : Z.land p 7 = p mod 8) by (apply (Z.land_ones p 3); lia).
        rewrite L7. apply zcanon_id. unfold M64. pose proof (Z.mod_pos_bound p 8 ltac:(lia)). revert H; clear; lia.
      - rewrite (ew_Ereg_extra regs3 _ 0). reflexivity.
      - exact Hp64. }
    assert (D35 : sv_denot (Ereg regs3 (e01_p2_extra p F sv0 bv0)) (SOff 35 0) = Z_to_bv 64 s).
    { apply bv_eq. rewrite denot_SOff, Z.add_0_r, U35. rewrite unsigned_lit_small by (revert Hs8; clear; lia).
      apply zcanon_id. unfold M64. revert Hs8; clear; lia. }
    lazymatch goal with |- SRr _ ?Wg (mkCfg ?msF ?mdF) _ =>
      lazymatch type of HS15 with st_ok _ ?Ev ?ssv _ =>
      apply (SRr_sym_branch rsegs Wg Ev ssv msF mdF _ BC_GE (SAlu ALU_AND (SOff 32 0) (SLit 7)) (SOff 35 0) HS15) end end;
    intros Hc4 HS16; clear HS15.
    * (* taken: the report call 0x8261c, not reached: p mod 8 = 0 < s *)
      exfalso. rewrite D1, D35 in Hc4. cbn [branch_taken] in Hc4.
      rewrite (RPgMem.rm_ra_slow_bv p s Hsok Hs0) in Hc4. discriminate Hc4.
    * (* not taken: 0x82618 `j 0x80164` *)
      aj_run_to E01_TBL_ok HS16 HJ9 E01_MALLOC. { e01_awr2 R (spZ regs) F pos U9 U10 U33 HRr HSTK HASTK. }
      e01_keep2 HFr KP2 R F U9 U10 U33.
      e01_fin HS16 HJ9 KP2 (RLEnv (spZ regs) R F 0 0 (rl_len pl') (bv_unsigned b0) (p + 1) (n - 1)) pl' W F mem3 HB Eab3 U33 SAV3 NWsav FLG3 NWflg;
      [ cbn [e_fl]; exact Rb0 | e01_tin_pos HJ9 W mem p n Hin Hnl b0 pl' Hpl Hin2 Hrq Hp4096 Hpc Hceilv Happ ].
Qed.
End b.

Check e01_ok.
Print Assumptions e01_ok.
