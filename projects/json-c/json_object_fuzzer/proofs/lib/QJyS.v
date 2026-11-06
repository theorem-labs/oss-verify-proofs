(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State StackLayout RiscvSemantics Run.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Export Q6q3.
Import ListNotations.

Class Amb : Type := mkAmb {
a_uid : word;
a_gid : word;
a_groups : list word;
a_net : NetQueue;
a_urandom : InputStream;
a_nofile : word;
a_sigmask : word;
a_hwcap : word;
a_abort : bool;
a_va : VaSize;
a_rnd : EntryDraw;
a_sp : word;
a_sp_valid : valid_sp a_sp
}.

Definition amb_creds {AMB : Amb} : Creds :=
mkCreds a_uid a_uid a_uid a_gid a_gid a_gid a_groups.

Definition mkModelC {AMB : Amb} (fds : list (word * FdEntry)) (vm : VmMaps)
(stdin : InputStream) (fs : Fs.Fs) (halted : option word)
(tid : option word) (rlim : option (list byte)) : Model :=
mkModelOf (mkFdState fds []) (mkVmState vm [] [])
(mkIoState stdin a_urandom a_net (Z_to_bv 64 0)) (mkFsState fs)
(mkProcState halted tid amb_creds false a_sigmask false None
false false false a_abort [])
(mkLimState rlim a_nofile)
(mkTimeState (Z_to_bv 64 0)).

Definition mkProcInputC {AMB : Amb} (argv envp : list (list byte)) (fs : Fs.Fs)
(stdin : InputStream) : ProcInput :=
mkProcInput_full argv envp fs stdin a_uid a_gid a_groups a_net a_nofile a_sigmask a_hwcap a_abort a_va a_urandom [].

Definition amb_of (inp : ProcInput) (rnd : EntryDraw) (sp : word) (Hsp : valid_sp sp) : Amb :=
mkAmb (in_uid inp) (in_gid inp) (in_groups inp) (in_net inp) (in_urandom inp)
(in_nofile inp) (in_sigmask inp) (in_hwcap inp) (in_abort_terminal inp) (in_va_size inp) rnd sp Hsp.

Lemma mkProcInputC_of_fs : forall inp rnd sp Hsp,
in_fs (@mkProcInputC (amb_of inp rnd sp Hsp) (in_argv inp) (in_envp inp) (in_fs inp) (in_stdin inp)) = in_fs inp.
Proof. intros. reflexivity. Qed.

Lemma mkProcInputC_of_argv : forall inp rnd sp Hsp,
in_argv (@mkProcInputC (amb_of inp rnd sp Hsp) (in_argv inp) (in_envp inp) (in_fs inp) (in_stdin inp)) = in_argv inp.
Proof. intros. reflexivity. Qed.

Lemma init_model_C_of : forall inp rnd sp Hsp reserved brk0 mbase sp0 lim,
init_model reserved brk0 mbase sp0 lim
(@mkProcInputC (amb_of inp rnd sp Hsp) (in_argv inp) (in_envp inp) (in_fs inp) (in_stdin inp))
= init_model reserved brk0 mbase sp0 lim inp.
Proof. intros. reflexivity. Qed.

Lemma a_rnd_of : forall inp rnd sp Hsp, @a_rnd (amb_of inp rnd sp Hsp) = rnd.
Proof. reflexivity. Qed.
Lemma a_hwcap_of : forall inp rnd sp Hsp, @a_hwcap (amb_of inp rnd sp Hsp) = in_hwcap inp.
Proof. reflexivity. Qed.
Lemma a_uid_of : forall inp rnd sp Hsp, @a_uid (amb_of inp rnd sp Hsp) = in_uid inp.
Proof. reflexivity. Qed.
Lemma a_sp_of : forall inp rnd sp Hsp, @a_sp (amb_of inp rnd sp Hsp) = sp.
Proof. reflexivity. Qed.

Section SpFacts.
Context {AMB : Amb}.
#[using="Type"] Lemma a_sp_lo : (0x7fff80000000 <= bv_unsigned a_sp)%Z.
Proof. destruct a_sp_valid as [H _]. exact H. Qed.
#[using="Type"] Lemma a_sp_hi : (bv_unsigned a_sp <= 0x800000000000)%Z.
Proof. destruct a_sp_valid as [_ [H _]]. exact H. Qed.
#[using="Type"] Lemma a_sp_al : (bv_unsigned a_sp mod 16 = 0)%Z.
Proof. destruct a_sp_valid as [_ [_ H]]. exact H. Qed.
End SpFacts.

Lemma with_tid_init_model_C : forall {AMB : Amb} reserved brk0 mbase sp lim av ev fs stdin tid,
with_tid tid (init_model reserved brk0 mbase sp lim (mkProcInputC av ev fs stdin))
= mkModelC [ (Z_to_bv 64 0, FdChannel (Z_to_bv 64 0));
(Z_to_bv 64 1, FdChannel (Z_to_bv 64 1));
(Z_to_bv 64 2, FdChannel (Z_to_bv 64 2)) ]
(mkVmMapsFull reserved [] [] brk0 brk0 lim mbase sp) stdin fs None (Some tid) None.
Proof. intros. reflexivity. Qed.

Lemma init_model_C : forall {AMB : Amb} reserved brk0 mbase sp lim av ev fs stdin,
init_model reserved brk0 mbase sp lim (mkProcInputC av ev fs stdin)
= mkModelC [ (Z_to_bv 64 0, FdChannel (Z_to_bv 64 0));
(Z_to_bv 64 1, FdChannel (Z_to_bv 64 1));
(Z_to_bv 64 2, FdChannel (Z_to_bv 64 2)) ]
(mkVmMapsFull reserved [] [] brk0 brk0 lim mbase sp) stdin fs None None None.
Proof. intros. reflexivity. Qed.

Section Proj.
Context {AMB : Amb}.
#[using="Type"] Lemma m_fds_C : forall fds vm si fs h t r, m_fds (mkModelC fds vm si fs h t r) = fds. Proof. reflexivity. Qed.
#[using="Type"] Lemma m_vmmaps_C : forall fds vm si fs h t r, m_vmmaps (mkModelC fds vm si fs h t r) = vm. Proof. reflexivity. Qed.
#[using="Type"] Lemma m_stdin_C : forall fds vm si fs h t r, m_stdin (mkModelC fds vm si fs h t r) = si. Proof. reflexivity. Qed.
#[using="Type"] Lemma m_fs_C : forall fds vm si fs h t r, m_fs (mkModelC fds vm si fs h t r) = fs. Proof. reflexivity. Qed.
#[using="Type"] Lemma m_halted_C : forall fds vm si fs h t r, m_halted (mkModelC fds vm si fs h t r) = h. Proof. reflexivity. Qed.
#[using="Type"] Lemma m_tid_C : forall fds vm si fs h t r, m_tid (mkModelC fds vm si fs h t r) = t. Proof. reflexivity. Qed.
#[using="Type"] Lemma m_killed_C : forall fds vm si fs h t r, m_killed (mkModelC fds vm si fs h t r) = None. Proof. reflexivity. Qed.
#[using="Type"] Lemma m_abort_terminal_C : forall fds vm si fs h t r, m_abort_terminal (mkModelC fds vm si fs h t r) = a_abort. Proof. reflexivity. Qed.
#[using="Type"] Lemma m_nofile_C : forall fds vm si fs h t r, m_nofile (mkModelC fds vm si fs h t r) = a_nofile. Proof. reflexivity. Qed.
#[using="Type"] Lemma m_sigmask_C : forall fds vm si fs h t r, m_sigmask (mkModelC fds vm si fs h t r) = a_sigmask. Proof. reflexivity. Qed.
#[using="Type"] Lemma m_vm_lazy_C : forall fds vm si fs h t r, m_vm_lazy (mkModelC fds vm si fs h t r) = []. Proof. reflexivity. Qed.
#[using="Type"] Lemma m_vm_materialized_C : forall fds vm si fs h t r, m_vm_materialized (mkModelC fds vm si fs h t r) = []. Proof. reflexivity. Qed.
#[using="Type"] Lemma with_fds_C : forall fds' fds vm si fs h t r,
with_fds fds' (mkModelC fds vm si fs h t r) = mkModelC fds' vm si fs h t r. Proof. reflexivity. Qed.
#[using="Type"] Lemma with_vmmaps_C : forall vm' fds vm si fs h t r,
with_vmmaps vm' (mkModelC fds vm si fs h t r) = mkModelC fds vm' si fs h t r. Proof. reflexivity. Qed.
#[using="Type"] Lemma with_stdin_C : forall si' fds vm si fs h t r,
with_stdin si' (mkModelC fds vm si fs h t r) = mkModelC fds vm si' fs h t r. Proof. reflexivity. Qed.
#[using="Type"] Lemma with_halted_C : forall c fds vm si fs h t r,
with_halted c (mkModelC fds vm si fs h t r) = mkModelC fds vm si fs (Some c) t r. Proof. reflexivity. Qed.
#[using="Type"] Lemma with_tid_C : forall t' fds vm si fs h t r,
with_tid t' (mkModelC fds vm si fs h t r) = mkModelC fds vm si fs h (Some t') r. Proof. reflexivity. Qed.
End Proj.

Definition rnd_bytes {AMB : Amb} : list byte := at_random_bytes (ed_random a_rnd).

Lemma length_rnd_bytes {AMB : Amb} : length rnd_bytes = 16%nat.
Proof. reflexivity. Qed.

Definition rnd_byte {AMB : Amb} (k : nat) : byte := nth k rnd_bytes (Z_to_bv 8 0).

Definition rnd_lo4 {AMB : Amb} : list byte := [rnd_byte 0; rnd_byte 1; rnd_byte 2; rnd_byte 3].
Definition rnd_hi4 {AMB : Amb} : list byte := [rnd_byte 4; rnd_byte 5; rnd_byte 6; rnd_byte 7].

Lemma rnd_lo4_eq {AMB : Amb} : rnd_lo4 = firstn 4 rnd_bytes.
Proof. reflexivity. Qed.
Lemma rnd_hi4_eq {AMB : Amb} : rnd_hi4 = firstn 4 (skipn 4 rnd_bytes).
Proof. reflexivity. Qed.

Definition canary_bytes {AMB : Amb} : list byte :=
[rnd_byte 0; Z_to_bv 8 0; rnd_byte 2; rnd_byte 3;
rnd_byte 4; rnd_byte 5; rnd_byte 6; rnd_byte 7].

Lemma length_canary_bytes {AMB : Amb} : length canary_bytes = 8%nat.
Proof. reflexivity. Qed.

Definition ssp_canary {AMB : Amb} : word := le_bytes_to_word canary_bytes.

Lemma bytes_le_to_Z_nonneg_A : forall bs, (0 <= bytes_le_to_Z bs)%Z.
Proof.
induction bs as [|b bs IH]; cbn [bytes_le_to_Z]; [lia|].
apply Z.lor_nonneg. split; [apply bv_unsigned_in_range|].
apply Z.shiftl_nonneg. exact IH.
Qed.

Lemma lor_lt_pow2_A : forall a b n, (0 <= a < 2^n)%Z -> (0 <= b < 2^n)%Z -> (Z.lor a b < 2^n)%Z.
Proof.
intros a b n Ha Hb.
destruct (Z.eq_dec a 0) as [->|Na]; [rewrite Z.lor_0_l; lia|].
destruct (Z.eq_dec b 0) as [->|Nb]; [rewrite Z.lor_0_r; lia|].
assert (Hn : (0 < n)%Z).
{ destruct (Z.lt_ge_cases 0 n) as [H|H]; [exact H|].
destruct (Z.eq_dec n 0) as [->|Nn]; [cbn in Ha; lia|].
rewrite Z.pow_neg_r in Ha by lia. lia. }
assert (Hpos : (0 < Z.lor a b)%Z).
{ pose proof (proj2 (Z.lor_nonneg a b) (conj (proj1 Ha) (proj1 Hb))).
destruct (Z.eq_dec (Z.lor a b) 0) as [E|E]; [|lia].
apply Z.lor_eq_0_iff in E. lia. }
apply Z.log2_lt_pow2; [exact Hpos|].
rewrite Z.log2_lor by lia.
apply Z.max_lub_lt; apply Z.log2_lt_pow2; lia.
Qed.

Lemma bytes_le_to_Z_bound_A : forall bs,
(bytes_le_to_Z bs < 2 ^ (8 * Z.of_nat (length bs)))%Z.
Proof.
induction bs as [|b bs IH]; cbn [bytes_le_to_Z length]; [cbn; lia|].
pose proof (bytes_le_to_Z_nonneg_A bs) as Hnn.
pose proof (bv_unsigned_in_range _ b) as Hb. unfold bv_modulus in Hb.
replace (8 * Z.of_nat (S (length bs)))%Z with (8 * Z.of_nat (length bs) + 8)%Z by lia.
apply lor_lt_pow2_A.
- assert (2 ^ 8 <= 2 ^ (8 * Z.of_nat (length bs) + 8))%Z by (apply Z.pow_le_mono_r; lia). lia.
- rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.pow_add_r by lia.
split; [lia|]. apply Z.mul_lt_mono_pos_r; [|exact IH]. lia.
Qed.

Lemma Z_to_le_bytes_to_Z_A : forall bs : list byte,
Z_to_le_bytes (length bs) (bytes_le_to_Z bs) = bs.
Proof.
induction bs as [|b bs IH]; [reflexivity|].
cbn [length Z_to_le_bytes bytes_le_to_Z].
pose proof (bytes_le_to_Z_nonneg_A bs) as Hnn.
pose proof (bv_unsigned_in_range _ b) as Hb. unfold bv_modulus in Hb.
f_equal.
- apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 8) with (2^8)%Z.
rewrite <- Z.land_ones by lia. rewrite Z.land_lor_distr_l.
rewrite (Z.land_ones (bv_unsigned b) 8) by lia. rewrite Z.mod_small by lia.
replace (Z.land (Z.shiftl (bytes_le_to_Z bs) 8) (Z.ones 8)) with 0%Z; [apply Z.lor_0_r|].
symmetry. rewrite Z.land_ones by lia. rewrite Z.shiftl_mul_pow2 by lia.
apply Z_mod_mult.
- rewrite Z.shiftr_lor, Z.shiftr_shiftl_l, Z.sub_diag, Z.shiftl_0_r by lia.
rewrite (Z.shiftr_div_pow2 (bv_unsigned b) 8) by lia. rewrite Z.div_small by lia.
rewrite Z.lor_0_l. exact IH.
Qed.

Lemma u_le_bytes_to_word : forall bs : list byte, (length bs <= 8)%nat ->
bv_unsigned (le_bytes_to_word bs) = bytes_le_to_Z bs.
Proof.
intros bs Hl. unfold le_bytes_to_word. rewrite Z_to_bv_unsigned. apply bv_wrap_small.
pose proof (bytes_le_to_Z_nonneg_A bs). pose proof (bytes_le_to_Z_bound_A bs).
unfold bv_modulus.
assert (2 ^ (8 * Z.of_nat (length bs)) <= 2 ^ 64)%Z by (apply Z.pow_le_mono_r; lia). lia.
Qed.

Lemma word_to_le_bytes_of_le : forall bs : list byte, (length bs <= 8)%nat ->
word_to_le_bytes (length bs) (le_bytes_to_word bs) = bs.
Proof.
intros bs Hl. unfold word_to_le_bytes. rewrite u_le_bytes_to_word by exact Hl.
apply Z_to_le_bytes_to_Z_A.
Qed.

Lemma ssp_canary_bytes {AMB : Amb} : word_to_le_bytes 8 ssp_canary = canary_bytes.
Proof. unfold ssp_canary. apply (word_to_le_bytes_of_le canary_bytes). rewrite length_canary_bytes. lia. Qed.

Lemma u_ssp_canary {AMB : Amb} : bv_unsigned ssp_canary = bytes_le_to_Z canary_bytes.
Proof. unfold ssp_canary. apply u_le_bytes_to_word. rewrite length_canary_bytes. lia. Qed.

Lemma canary_bytes_length {AMB : Amb} : length canary_bytes = 8%nat.
Proof. reflexivity. Qed.

Lemma canary_byte1 {AMB : Amb} : forall d, nth 1 canary_bytes d = Z_to_bv 8 0.
Proof. reflexivity. Qed.

Lemma canary_bytes_nth {AMB : Amb} : forall k d, (k < 8)%nat -> k <> 1%nat ->
nth k canary_bytes d = rnd_byte k.
Proof.
intros k d Hk H1.
destruct k as [|[|[|[|[|[|[|[|k]]]]]]]]; try reflexivity; [contradiction|lia].
Qed.

Lemma rnd_bytes_eq {AMB : Amb} :
rnd_bytes = [rnd_byte 0; rnd_byte 1; rnd_byte 2; rnd_byte 3; rnd_byte 4; rnd_byte 5; rnd_byte 6; rnd_byte 7;
rnd_byte 8; rnd_byte 9; rnd_byte 10; rnd_byte 11; rnd_byte 12; rnd_byte 13; rnd_byte 14; rnd_byte 15].
Proof. reflexivity. Qed.

Definition secret_bytes {AMB : Amb} : list byte :=
[rnd_byte 8; rnd_byte 9; rnd_byte 10; rnd_byte 11;
rnd_byte 12; rnd_byte 13; rnd_byte 14; rnd_byte 15].

Lemma secret_bytes_length {AMB : Amb} : length secret_bytes = 8%nat.
Proof. reflexivity. Qed.

Definition ssp_secret {AMB : Amb} : word := le_bytes_to_word secret_bytes.

Definition rnd_secret {AMB : Amb} : Z := bv_unsigned ssp_secret.

Lemma ssp_secret_bytes {AMB : Amb} : word_to_le_bytes 8 ssp_secret = secret_bytes.
Proof. unfold ssp_secret. apply (word_to_le_bytes_of_le secret_bytes). rewrite secret_bytes_length. lia. Qed.

Lemma u_ssp_secret {AMB : Amb} : bv_unsigned ssp_secret = bytes_le_to_Z secret_bytes.
Proof. unfold ssp_secret. apply u_le_bytes_to_word. rewrite secret_bytes_length. lia. Qed.

Lemma rnd_secret_range {AMB : Amb} : (0 <= rnd_secret < 2^64)%Z.
Proof. unfold rnd_secret. pose proof (bv_unsigned_in_range _ ssp_secret) as H. unfold bv_modulus in H. exact H. Qed.

Lemma rnd_secret_eq {AMB : Amb} : rnd_secret = bytes_le_to_Z secret_bytes.
Proof. unfold rnd_secret. apply u_ssp_secret. Qed.

Lemma skipn8_rnd_bytes {AMB : Amb} : skipn 8 rnd_bytes = secret_bytes.
Proof. reflexivity. Qed.

Lemma rnd_bytes_split {AMB : Amb} :
rnd_bytes = [rnd_byte 0; rnd_byte 1; rnd_byte 2; rnd_byte 3; rnd_byte 4; rnd_byte 5; rnd_byte 6; rnd_byte 7] ++ secret_bytes.
Proof. reflexivity. Qed.

Lemma amb_rc_ceil_range {AMB : Amb} :
(0x7fff7f800000 <= bv_unsigned a_sp - 8388608 <= 0x7fffff800000)%Z.
Proof. pose proof a_sp_lo. pose proof a_sp_hi. lia. Qed.

Lemma amb_rc_ceil_al16 {AMB : Amb} : ((bv_unsigned a_sp - 8388608) mod 16 = 0)%Z.
Proof.
pose proof a_sp_al as H. rewrite Zminus_mod, H. reflexivity.
Qed.

#[global] Instance amb_rc {AMB : Amb} : RunConsts := {|
rc_ceil := (bv_unsigned a_sp - 8388608)%Z;
rc_canary := ssp_canary;
rc_secret := rnd_secret;
rc_ceil_range := amb_rc_ceil_range;
rc_ceil_al16 := amb_rc_ceil_al16;
rc_secret_range := rnd_secret_range |}.

Lemma rc_ceil_amb {AMB : Amb} : rc_ceil = (bv_unsigned a_sp - 8388608)%Z.
Proof. reflexivity. Qed.
Lemma alloc_ceiling_amb {AMB : Amb} : alloc_ceiling = (bv_unsigned a_sp - 8388608)%Z.
Proof. reflexivity. Qed.
Lemma rc_canary_amb {AMB : Amb} : rc_canary = ssp_canary.
Proof. reflexivity. Qed.
Lemma rc_secret_amb {AMB : Amb} : rc_secret = rnd_secret.
Proof. reflexivity. Qed.
