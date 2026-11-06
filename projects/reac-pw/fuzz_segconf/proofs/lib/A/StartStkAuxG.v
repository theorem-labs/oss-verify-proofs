From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.reac_pw.fuzz_segconf.images Require Import Asan.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YK11.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK00 YK0c YK0e YK09 YA01 YA0c YA0e YA02 YA03 YA0j YP09.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A Require Import AB12 AB1h.
Import ListNotations. Import AX2. Import AX2S. Import APG. Import APSG.
Open Scope Z_scope.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
(* At a hand-off state ch of the start-up certificate whose knowledge reads the 20 auxv words and the 16 AT_RANDOM bytes
   (stk_aux_chk ch = true; every state of A/AB01.v does, StartStkAux.tfib_holes_stkaux), the bytes of the entry stack
   block above the entry sp + 24 that argH0 leaves out (YA02.v argH0_false_cases) are present in the hand-off memory:
   [usp + 8 argc + 8 envc + 24, + 184) and [usp + |bsb| - 16, usp + |bsb|). *)
Definition STK_AUX_READS : list (expr * Z) :=
map (fun n : nat => (fst e_auxb, snd e_auxb + 8 * Z.of_nat n)) (seq 0 20) ++ [(fst e_atrb, snd e_atrb); (fst e_atrb, snd e_atrb + 8)].
Definition stk_aux_chk (ch : acs) : bool :=
forallb (fun p => match kn_read TSEGS ch (fst p) (snd p) 8 with Some _ => true | None => false end) STK_AUX_READS.
Lemma snd_auxb : snd e_auxb = 24.
Proof. vm_compute. reflexivity. Qed.
Lemma snd_atrb : snd e_atrb = 184.
Proof. vm_compute. reflexivity. Qed.
Lemma stk_aux_rom_none : forall z, 0x601000 <= z < 2 ^ 64 -> YK11.seg_rom TSEGS (Z_to_bv 64 z) = None.
Proof.
intros z Hz. apply seg_rom_none_of_find. apply tfib_in_hull.
rewrite u64_lit by lia. unfold in_hull. apply andb_false_iff. right. apply Z.ltb_ge.
change (img_hi TFIB) with 0x601000. lia.
Qed.
Lemma split_val : forall (E : env) e, 0 <= snd (split_lit e) -> snd (split_lit e) <= uE E e ->
uE E (fst (split_lit e)) + snd (split_lit e) = uE E e.
Proof.
intros E e. destruct (split_lit e) as [b k] eqn:Hs. cbn [fst snd]. intros Hk Hle.
pose proof (split_lit_denot E e b k Hs) as D. unfold uE in *. rewrite D in Hle |- *.
rewrite Z_to_bv_unsigned in Hle |- *. pose proof (YK11.u64_range (edenot E b)) as Rb.
unfold bv_wrap, bv_modulus in *. change (2 ^ Z.of_N 64) with (2 ^ 64) in *. lia.
Qed.
Section s.
Variables (sp : word) (rdraw : EntryDraw) (brk : word) (inp : ProcInput) (ch : acs) (E : env)
(R : bvmap 5 word) (FULL : word -> option byte) (model : Model).
Hypothesis Hsp : valid_sp sp.
Hypothesis Hva : valid_argv (in_argv inp).
Hypothesis Hve : valid_envp (in_envp inp).
Hypothesis Hfit : entry_stack_fits sp (in_argv inp) (in_envp inp).
Hypothesis Hchk : stk_aux_chk ch = true.
Hypothesis HC : cs_ok TSEGS TFIB YA02.LIMIT (YA02.TOP sp)
(SINV0 TPH sp rdraw brk (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp))
(argH0 TPH sp rdraw (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) (in_fs inp) E ch R FULL model.
#[local] Notation bsb := (build_stack_bytes TPH sp (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) rdraw).
Lemma stk_aux_agree : forall e, nb_lt NX0G e = true ->
uE E e = uE (E0 TPH sp rdraw brk (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) e.
Proof.
intros e He. destruct (co_sinv _ _ _ _ _ _ _ _ _ _ _ _ HC) as (Hag & _ & _).
unfold uE. rewrite (edenot_ev_agree NX0G E _ e He Hag). reflexivity.
Qed.
Lemma u_auxb : uE E (fst e_auxb) = bv_unsigned sp + 8 * Z.of_nat (length (in_argv inp)) + 8 * Z.of_nat (length (in_envp inp)).
Proof.
pose proof (u_e_auxv TPH sp rdraw brk (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) Hsp Hva Hve Hfit) as U.
rewrite <- (stk_aux_agree e_auxv eq_refl) in U.
pose proof (split_val E e_auxv) as S. fold e_auxb in S. rewrite snd_auxb, U in S.
pose proof (proj1 Hsp) as B1. unfold sp_window_lo in B1.
specialize (S ltac:(lia) ltac:(lia)). lia.
Qed.
Lemma u_atrb : uE E (fst e_atrb) = bv_unsigned sp + Z.of_nat (length bsb) - 200.
Proof.
pose proof (u_e_atrandom TPH sp rdraw brk (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) Hsp Hva Hve Hfit) as U.
rewrite <- (stk_aux_agree e_atrandom eq_refl) in U.
pose proof (split_val E e_atrandom) as S. fold e_atrb in S. rewrite snd_atrb, U in S.
pose proof (proj1 Hsp) as B1. unfold sp_window_lo in B1.
specialize (S ltac:(lia) ltac:(lia)). lia.
Qed.
Lemma stk_aux_read_present : forall b k, In (b, k) STK_AUX_READS -> forall i, 0 <= i < 8 ->
0x601000 <= uE E b + k + i < 2 ^ 64 -> FULL (Z_to_bv 64 (uE E b + k + i)) <> None.
Proof.
intros b k Hin i Hi Hr.
pose proof Hchk as Hc. unfold stk_aux_chk in Hc.
pose proof (proj1 (forallb_forall _ _) Hc (b, k) Hin) as Hk. cbv beta in Hk. cbn [fst snd] in Hk.
destruct (kn_read TSEGS ch b k 8) as [v|] eqn:Hv; [|discriminate Hk].
destruct (ho_read _ _ _ _ _ _ _ _ _ _ _ _ HC b k 8%nat v Hv) as (bs & Hrd & Hlen & _).
assert (Ea : adenot E {| a_base := b; a_off := k |} = Z_to_bv 64 (uE E b + k)) by reflexivity.
rewrite Ea in Hrd.
apply (proj1 (rdn_mbytes TSEGS _ 8 (uE E b + k) bs)) in Hrd as [_ Hb].
specialize (Hb (Z.to_nat i) ltac:(lia)). rewrite Z2Nat.id in Hb by lia.
assert (Hn : nth_error bs (Z.to_nat i) <> None) by (apply nth_error_Some; lia).
unfold mbyte in Hb.
match type of Hb with context [match ?M (Z_to_bv 64 ?x) with _ => _ end] =>
destruct (M (Z_to_bv 64 x)) as [bb|] eqn:Em end.
- rewrite (ho_Mr_full _ _ _ _ _ _ _ _ _ Em). discriminate.
- rewrite (stk_aux_rom_none _ Hr) in Hb. rewrite <- Hb in Hn. exfalso. exact (Hn eq_refl).
Qed.
Lemma stk_aux_present : forall a,
(bv_unsigned sp + 8 * Z.of_nat (length (in_argv inp)) + 8 * Z.of_nat (length (in_envp inp)) + 24 <= a
< bv_unsigned sp + 8 * Z.of_nat (length (in_argv inp)) + 8 * Z.of_nat (length (in_envp inp)) + 184)
\/ (bv_unsigned sp + Z.of_nat (length bsb) - 16 <= a < bv_unsigned sp + Z.of_nat (length bsb)) ->
FULL (Z_to_bv 64 a) <> None.
Proof.
intros a Ha. pose proof (proj1 Hsp) as B1. unfold sp_window_lo in B1.
pose proof (proj1 (proj2 Hsp)) as B3. unfold sp_window_hi in B3. pose proof (proj1 Hva) as VA. pose proof (proj1 Hve) as VE.
pose proof (usp_fit TPH sp rdraw (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) Hfit) as B2.
pose proof u_auxb as UA. pose proof u_atrb as UR.
destruct Ha as [Ha|Ha].
- pose proof (Z.div_mod (a - uE E (fst e_auxb) - 24) 8 ltac:(lia)) as D.
pose proof (Z.mod_pos_bound (a - uE E (fst e_auxb) - 24) 8 ltac:(lia)) as M.
set (j := (a - uE E (fst e_auxb) - 24) / 8) in *. set (i := (a - uE E (fst e_auxb) - 24) mod 8) in *.
assert (Hj : 0 <= j < 20) by lia.
assert (Hin : In (fst e_auxb, snd e_auxb + 8 * Z.of_nat (Z.to_nat j)) STK_AUX_READS).
{ unfold STK_AUX_READS. apply in_or_app. left.
apply (in_map (fun n : nat => (fst e_auxb, snd e_auxb + 8 * Z.of_nat n)) (seq 0 20) (Z.to_nat j)).
apply in_seq. lia. }
rewrite snd_auxb, Z2Nat.id in Hin by lia.
replace a with (uE E (fst e_auxb) + (24 + 8 * j) + i) by lia.
apply (stk_aux_read_present _ _ Hin i ltac:(lia)). lia.
- destruct (Z_lt_le_dec (a - uE E (fst e_atrb) - 184) 8) as [L|L].
+ assert (Hin : In (fst e_atrb, snd e_atrb) STK_AUX_READS).
{ unfold STK_AUX_READS. apply in_or_app. right. left. reflexivity. }
rewrite snd_atrb in Hin.
replace a with (uE E (fst e_atrb) + 184 + (a - uE E (fst e_atrb) - 184)) by lia.
apply (stk_aux_read_present _ _ Hin (a - uE E (fst e_atrb) - 184) ltac:(lia)). lia.
+ assert (Hin : In (fst e_atrb, snd e_atrb + 8) STK_AUX_READS).
{ unfold STK_AUX_READS. apply in_or_app. right. right. left. reflexivity. }
rewrite snd_atrb in Hin.
replace a with (uE E (fst e_atrb) + (184 + 8) + (a - uE E (fst e_atrb) - 192)) by lia.
apply (stk_aux_read_present _ _ Hin (a - uE E (fst e_atrb) - 192) ltac:(lia)). lia.
Qed.
End s.
