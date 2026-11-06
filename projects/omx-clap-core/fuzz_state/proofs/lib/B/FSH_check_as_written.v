(* Modified by Theorem Labs, 2026-10: lib/B (fs.asan-ubsan) twin of lib/A/FSH_check_as_written.v
   (a working branch c799c60f5cf), the same glue over B's own segment lemmas.
   rule 24: proves function check_as_written (B 0x8164c, CONFIRM by a Theorem Labs lane); none ported, written new;
   template lib/A/FSH_check_as_written.v. *)
(*
   check_as_written 0x8164c (fs.c:165-186), 324 instructions of fs.asan-ubsan: the ASSEMBLY of the CHECKS lane's ASan
   walk - it glues the B segment lemmas into
       check_as_written_proof : check_as_written_spec tfibsegs B
   (the statement is lib/B/FSH_Fn_checks.v, Section c, and is never edited here).

   The segments, in the order the walk takes them (every one a merged lemma):
   - front   0x8164c .. 0x8170c (prologue, strlen, the two mallocs, t[0]) or .. 0x81810 (the empty text)
                                                      lib/B/FSW_caw_front.v  caw_front
   - scan    0x8170c .. 0x81804 (the NUL) / 0x81a78 (a refused character, s5 = SIZE_MAX)
                                                      lib/B/FSW_caw_scan.v  caw_scan_loop
   - re-key  0x81804 (caw_ssX -> cawt_ss)             lib/B/FSW_caw_rekey.v  caw_rekey_tail
             0x81a78 (caw_ssB -> caa_xss, n = SIZE_MAX)                       caw_rekey_break
   - tail    0x81804 .. 0x81a78 (more than two '=')   lib/B/FSW_caw_tail.v  cawt_refuse_pad
   - accept  0x81804 .. 0x81a78 / 0x818ac             lib/B/FSW_caw_accept.v  caa_refuse_tail / caa_accept_m0 /
                                                      caa_accept_emit (caa_mkexit re-keys the pad refusal's exit)
   - empty   0x81810 .. 0x81a78 (the empty text)      lib/B/FSW_caw_empty.v  caw_empty_tail
   - emit    0x818ac .. 0x81a78                       lib/B/FSW_caw_emit.v  caw_emit_loop
   - emit-x  0x81a78 (cae_exit_ss -> caa_xss)         lib/B/FSW_caw_emitx.v  caw_emit_exit
   - back    0x81a78 .. the return                    lib/B/FSW_caw_backE.v  cawb_enter
   Between them this file re-keys the emit loop's exit env (caw_emit_exit_env) and carries want's shadow across the
   scan (caw_ra_keep2). A -> B: B's scan leaves at two pcs, so the refused character is not a tail arm here (A's
   cawt_refuse_byte / _byte_pad); the empty-text hand-over already has atom 38 = 0 (A's caw_set38 is not needed);
   the frame is 64 bytes (A 48); B keeps the answer n in s5 (atom 49 of caa_xss, A's s3); the front's env pins
   only the entry registers below 30 (atoms 30 / 31 hold ~six and ra), which covers every register the back reads.

   The answer the walk computes is WriterSpec.b64_dec tb (lib/Prog/WriterSpec.v:110): the scan refuses, or more
   than two '=' were read, or the sextet tail is wrong -> n = SIZE_MAX; otherwise n = |six_bytes sx| and want
   holds six_bytes sx. The four refusal / three accept arms below are exactly b64_dec's cases.

   Section hypotheses (owners): IMG (S0, lib/B/FSH_Rt.v), SYMS (RELOC, lib/B/FSH_Base.v), RTs / RTb / RTm / RTf
   (RUNTIME: lib/B/FSH_Rt.v FsRt's fr_strlen, fr_bcmp, fr_malloc, fr_free by their field types, the only four FsRt
   fields the walk uses), FS_ENV / ML (the API environment and the model laws) - the stated interfaces the front and
   the back half take. Every segment above is a merged lemma; this file adds the glue only. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP05 YL01 YL02 YL07 YL09.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSupoison FSupoisonU FSH_YC20 FSH_Gen.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import
YB1v YF0l YB1w FSH_Base FSH_Rt FSW_K FSW_caw_defs FSW_caw_model FSW_caw_tail FSW_caw_scan FSW_caw_emit
FSW_caw_accept FSW_caw_rekey FSW_caw_emitx FSW_caw_front FSW_caw_empty FSW_caw_back FSW_caw_backE FSH_Fn_checks.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require WriterSpec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.

(* ---- pure facts about the decoder (lib/Prog/WriterSpec.v) ---- *)
(* |six_bytes sx| = 3 * (|sx| / 4) + (0, 0, 1, 2 for |sx| mod 4 = 0, 1, 2, 3), hence at most 3 * (|sx| / 4) + 2 *)
Lemma caw_sixb_len_n : forall n sx, (length sx <= n)%nat ->
  (length (WriterSpec.six_bytes sx) <= 3 * (length sx / 4) + 2)%nat.
Proof.
induction n as [|n IH]; intros sx Hn;
  destruct sx as [|a [|b [|c [|d sx']]]]; cbn [WriterSpec.six_bytes length] in *; try lia.
- assert (H4 : (4 + length sx' = S (S (S (S (length sx')))))%nat) by lia.
  assert (HD : ((S (S (S (S (length sx'))))) / 4 = 1 + length sx' / 4)%nat).
  { replace (S (S (S (S (length sx')))))%nat with (1 * 4 + length sx')%nat by lia.
    rewrite Nat.div_add_l by lia. lia. }
  rewrite HD. pose proof (IH sx' ltac:(lia)) as Hsx'. lia.
Qed.
Lemma caw_sixb_len : forall sx, (length (WriterSpec.six_bytes sx) <= 3 * (length sx / 4) + 2)%nat.
Proof. intros sx. exact (caw_sixb_len_n (length sx) sx ltac:(lia)). Qed.
(* the answer fits the block the function asked for: |six_bytes sx| <= b64_alloc_bound |tb| when |sx| <= |tb| *)
Lemma caw_sixb_bound : forall (sx tb : list Z), (length sx <= length tb)%nat ->
  Z.of_nat (length (WriterSpec.six_bytes sx)) <= b64_alloc_bound (Z.of_nat (length tb)).
Proof.
intros sx tb Hle. pose proof (caw_sixb_len sx) as HL.
assert (HZ : Z.of_nat (length (WriterSpec.six_bytes sx)) <= 3 * Z.of_nat (length sx / 4) + 2) by lia.
rewrite Nat2Z.inj_div in HZ. cbn [Z.of_nat] in HZ.
assert (HD : Z.of_nat (length sx) / 4 <= Z.of_nat (length tb) / 4)
  by (apply Z.div_le_mono; lia).
unfold b64_alloc_bound. lia.
Qed.
(* b64_dec's three None cases and its Some case, read off b64_scan's answer *)
Lemma caw_dec_none_scan : forall tb, WriterSpec.b64_scan 0 [] tb = None -> WriterSpec.b64_dec tb = None.
Proof. intros tb H. unfold WriterSpec.b64_dec. rewrite H. reflexivity. Qed.
Lemma caw_dec_pad : forall tb sx pad, WriterSpec.b64_scan 0 [] tb = Some (sx, pad) -> 3 <= pad ->
  WriterSpec.b64_dec tb = None.
Proof.
intros tb sx pad H Hp. unfold WriterSpec.b64_dec. rewrite H.
replace (pad <=? 2) with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
Qed.
Lemma caw_dec_tail : forall tb sx pad, WriterSpec.b64_scan 0 [] tb = Some (sx, pad) ->
  WriterSpec.six_tail_ok sx = false -> WriterSpec.b64_dec tb = None.
Proof.
intros tb sx pad H Ht. unfold WriterSpec.b64_dec. rewrite H, Ht. rewrite andb_false_r. reflexivity.
Qed.
Lemma caw_dec_some : forall tb sx pad, WriterSpec.b64_scan 0 [] tb = Some (sx, pad) -> 0 <= pad <= 2 ->
  WriterSpec.six_tail_ok sx = true -> WriterSpec.b64_dec tb = Some (WriterSpec.six_bytes sx).
Proof.
intros tb sx pad H Hp Ht. unfold WriterSpec.b64_dec. rewrite H, Ht.
replace (pad <=? 2) with true by (symmetry; apply Z.leb_le; lia). reflexivity.
Qed.

Section A.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.

(* ---- the stated interfaces this walk rests on ---- *)
Hypothesis IMG : fs_img_facts tfibsegs B.
Hypothesis SYMS : FsShadowSyms B.
Hypothesis RTs : astrlen_realizesU tfibsegs B PC_strlen.
Hypothesis RTb : FSupoisonU.abcmp_realizesU tfibsegs B PC_bcmp.
Hypothesis RTm : pc_wrap_malloc (as_code B) = PC_malloc /\ FSupoisonU.amalloc_realizesU tfibsegs B.
Hypothesis RTf : pc_wrap_free (as_code B) = PC_free /\ FSupoisonU.afree_realizesU tfibsegs B.
Hypothesis FS_ENV : api_env tfibsegs B.
Hypothesis ML : model_laws (as_universe B).

(* the spec's post is FSW_caw_back.v's cawb_post, the post cawb_enter proves; the sink instance SK is passed by name
   (a Theorem Labs lane 06:50Z: never leave a sink argument to instance resolution) *)

(* ================= the glue ================= *)
Let LAWS : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.

(* a live block lies in application memory (the AR blocks law, YG0d.v:430) *)
Lemma caw_inapp_block : forall ly S U (W : world tfibsegs) mem md p n,
  ARU tfibsegs B ly S U W mem md -> In (p, n) (ablocks B ly S) -> 1 <= n -> in_app p n.
Proof.
intros ly S U W mem md p n HARU Hin Hn.
destruct (al_blocks _ _ LAWS ly S W (unpoison U mem) md p n (ARU_AR tfibsegs B ly S U W mem md HARU) Hin)
  as (_ & _ & _ & Happ & _).
unfold req_size in Happ. replace (n =? 0) with false in Happ by (symmetry; apply Z.eqb_neq; lia). exact Happ.
Qed.

(* the shadow of an application range survives a change of memory outside two windows (the twin of FSW_caw_emit.v
   cae_ra_keep with two windows: the scan loop writes six[m] and its frame). A window in low memory may end up to
   512 bytes above kLowShadowBeg: the shadow bytes of a range at or above 4096 start at SHADOW_OFF + 512. *)
Lemma caw_ra_keep2 : forall (W' : world tfibsegs) (m1 m2 : word -> option byte) (a len lo1 hi1 lo2 hi2 : Z),
  range_addressable (rd_of tfibsegs (mrestrict (w_H W') m1)) SHADOW_OFF a len ->
  (forall x : word, ~ (lo1 <= bv_unsigned x < hi1) -> ~ (lo2 <= bv_unsigned x < hi2) -> m2 x = m1 x) ->
  (hi1 <= SHADOW_OFF + 512 \/ kHighMemBeg <= lo1) ->
  (hi2 <= SHADOW_OFF + 512 \/ kHighMemBeg <= lo2) ->
  4096 <= a -> a + len <= CAW_CEIL ->
  range_addressable (rd_of tfibsegs (mrestrict (w_H W') m2)) SHADOW_OFF a len.
Proof.
intros W' m1 m2 a len lo1 hi1 lo2 hi2 HRA Hfr Happ1 Happ2 Ha0 Ha1 x Hx.
destruct (HRA x Hx) as (s & Hs & Hok). exists s. split; [|exact Hok].
rewrite <- Hs. unfold rd_of. f_equal.
assert (HD : CAW_CEIL / 8 = 17592184995840) by (vm_compute; reflexivity).
assert (Hc : SHADOW_OFF + 512 <= shadow_of_addr SHADOW_OFF x < kHighMemBeg).
{ unfold shadow_of_addr. assert (H1 : 4096 / 8 <= x / 8) by (apply Z.div_le_mono; lia).
  assert (H2 : x / 8 <= CAW_CEIL / 8) by (apply Z.div_le_mono; lia).
  rewrite HD in H2. change (4096 / 8) with 512 in H1. unfold SHADOW_OFF, kHighMemBeg in *. lia. }
assert (Heq : mrestrict (w_H W') m2 (Z_to_bv 64 (shadow_of_addr SHADOW_OFF x))
            = mrestrict (w_H W') m1 (Z_to_bv 64 (shadow_of_addr SHADOW_OFF x))).
{ unfold mrestrict. destruct (w_H W' (Z_to_bv 64 (shadow_of_addr SHADOW_OFF x))); [reflexivity|].
  apply Hfr; rewrite Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 64) with (2 ^ 64);
    rewrite Z.mod_small by (unfold SHADOW_OFF, kHighMemBeg in *; lia);
    unfold kHighMemBeg, SHADOW_OFF in *; lia. }
unfold YP09.mbyte. rewrite Heq. reflexivity.
Qed.

(* the back half, entered from any arm at 0x81a78 in caa_xss with the answer n in atom 49; the env agrees with the
   entry registers below 30 (the front's env: atoms 30 / 31 are ~six and ra), which holds every register the back
   half reads (ra = 1, the callee-saved ones, a1 = 11, a2 = 12) *)
Lemma caw_back : forall ly S U W regs mem md ch bd l (tb : list Z) live peak cnt fail
    W2 ly2 S2 want six E ms mdc n,
  fpreU tfibsegs B STK_check_as_written ly S U W regs mem md ch -> fs_heads B ly S U ->
  getr regs 11 = w64 bd -> getr regs 12 = w64 l -> Z.of_nat (length tb) <= PRESET_FILE_MAX_BYTES ->
  caw_answerA tfibsegs B ly S U W mem tb bd l -> fs_glob tfibsegs W mem live peak cnt fail ->
  st_nev S + EV_check_as_written <= EV_MAX ->
  ablocks B ly2 S2 = (ablocks B ly S ++ [(want, cawf_want_size tb)]) ++ [(six, cawf_six_size tb)] ->
  (forall m, ~ In (want, m) (ablocks B ly S)) -> (forall m, ~ In (six, m) (ablocks B ly S)) ->
  st_ok tfibsegs E caa_xss (restrict (w_H W2) ms) ->
  (forall k, (k < 30)%nat -> ew E k = getr regs (Z_to_bv 5 (Z.of_nat k))) ->
  ew E 33 = Z_to_bv 64 six -> ew E 34 = Z_to_bv 64 want -> ew E 49 = Z_to_bv 64 n ->
  ajournal tfibsegs B STK_check_as_written (spZ regs) [] ly S W (unpoison U mem) md [] ly2 S2 W2
    (unpoison U (ms_mem ms)) mdc 2 ->
  ARU tfibsegs B ly2 S2 U W2 (ms_mem ms) mdc ->
  (WriterSpec.b64_dec tb = None -> n = SIZE_MAXZ) ->
  (forall bs, WriterSpec.b64_dec tb = Some bs ->
     n = Z.of_nat (length bs) /\ n <= b64_alloc_bound (Z.of_nat (length tb)) /\
     caw_bytes W2 (ms_mem ms) want bs) ->
  SRr tfibsegs W2 (mkCfg ms mdc) (@cawb_post fx rc SK B regs ly S U W mem md live peak cnt fail).
Proof.
intros ly S U W regs mem md ch bd l tb live peak cnt fail W2 ly2 S2 want six E ms mdc n
  HPRE FH H11 H12 Hlen HANS HG Hev Hbl Hfw Hf6 HS HENT E33 E34 E49 HJ HARU HNONE HSOME.
assert (HR : forall r : bv 5, bv_unsigned r < 30 -> ew E (Z.to_nat (bv_unsigned r)) = getr regs r).
{ intros r Hr. pose proof (bv_unsigned_in_range 5 r) as Hrg.
  rewrite (HENT (Z.to_nat (bv_unsigned r)) ltac:(lia)). rewrite Z2Nat.id by lia.
  rewrite Z_to_bv_bv_unsigned. reflexivity. }
apply (@cawb_enter fx rc SK B IMG FS_ENV ML RTb RTf ly S U W regs mem md ch bd l tb live peak cnt fail
         E ms mdc ly2 S2 W2 six want n HPRE FH H11 H12 Hlen HANS HG Hev HS).
- exact (HR 1%bv ltac:(vm_compute; reflexivity)).
- intros r Hr. apply HR. unfold acallee_saved in Hr. lia.
- exact (HR 11%bv ltac:(vm_compute; reflexivity)).
- exact (HR 12%bv ltac:(vm_compute; reflexivity)).
- exact E33.
- exact E34.
- exact E49.
- exact HJ.
- exact HARU.
- exact Hbl.
- exact Hfw.
- exact Hf6.
- exact HNONE.
- exact HSOME.
Qed.

(* ---- small facts the arms share ---- *)
(* the atoms the NUL-exit re-key keeps (FSW_caw_rekey.v cawr_P) include every atom below 40 *)
Lemma caw_rP_lt40 : forall n, (n < 40)%nat -> cawr_P n = true.
Proof.
intros n Hn. unfold cawr_P.
destruct (Nat.eqb_spec n 40); [lia|]. destruct (Nat.eqb_spec n 43); [lia|].
destruct (Nat.ltb_spec 49 n); [lia|]. reflexivity.
Qed.
(* the register obligations of a re-key onto caa_xss: every atom from 44 up is set by the extension list *)
Ltac caw_lk EL LD :=
  lazymatch goal with
  | |- ew _ ?j = _ =>
      let jj := eval compute in (Nat.sub j 44) in
      change j with (44 + jj)%nat; rewrite (EL jj ltac:(lia)); unfold LD; cbn [nth]; reflexivity
  end.
(* the emit loop's exit re-keyed onto caa_xss (FSW_caw_emitx.v caw_emit_exit), with the env it needs: the fresh
   atoms 44 .. 61 of caa_xregs from a1 a2 s3 s6 _ s5 t0 t1 t2 _ _ a5 a6 a7 t3 t4 t5 t6 (the list of
   FSW_caw_rekey.v caw_rekey_break); atom 49 is s5, the loop's atom 49 *)
Lemma caw_emit_exit_env : forall (W' : world tfibsegs) (E1 : env) (ms0 ms1 : machine_state) (sp0 : Z),
  st_ok tfibsegs E1 cae_exit_ss (restrict (w_H W') ms1) ->
  region_ok tfibsegs E1 (ms_mem (restrict (w_H W') ms0)) caw_stk ->
  bv_unsigned (ew E1 2) = sp0 ->
  (forall x : word, sp0 - 64 <= bv_unsigned x < sp0 -> ms_mem ms1 x = ms_mem ms0 x) ->
  mem_grows (mrestrict (w_H W') (ms_mem ms0)) (mrestrict (w_H W') (ms_mem ms1)) ->
  exists E2, env_agree 44 E1 E2 /\ st_ok tfibsegs E2 caa_xss (restrict (w_H W') ms1) /\ ew E2 49 = ew E1 49.
Proof.
intros W' E1 ms0 ms1 sp0 HS HRG Esp HFR HGR.
set (LD := [getr (ms_regs ms1) 11%bv; getr (ms_regs ms1) 12%bv; getr (ms_regs ms1) 19%bv;
            getr (ms_regs ms1) 22%bv; Z_to_bv 64 0; getr (ms_regs ms1) 21%bv;
            getr (ms_regs ms1) 5%bv; getr (ms_regs ms1) 6%bv; getr (ms_regs ms1) 7%bv;
            Z_to_bv 64 0; Z_to_bv 64 0;
            getr (ms_regs ms1) 15%bv; getr (ms_regs ms1) 16%bv; getr (ms_regs ms1) 17%bv;
            getr (ms_regs ms1) 28%bv; getr (ms_regs ms1) 29%bv; getr (ms_regs ms1) 30%bv;
            getr (ms_regs ms1) 31%bv]).
set (E2 := extK E1 44 LD).
assert (EL : forall j, (j < 18)%nat -> ew E2 (44 + j) = nth j LD (Z_to_bv 64 0))
  by (intros j Hj; unfold E2; apply cae_ext_lookup; unfold LD; cbn [length]; lia).
assert (HAG : env_agree 44 E1 E2) by (unfold E2; apply env_agree_extK).
exists E2. split; [exact HAG|]. split.
- apply (@caw_emit_exit fx W' E1 E2 ms0 ms1 sp0 HS HRG Esp HFR HGR HAG).
  apply Forall_forall. intros rj Hin. vm_compute in Hin.
  repeat (destruct Hin as [<-|Hin]); [..|destruct Hin]; cbn [fst snd]; caw_lk EL LD.
- change 49%nat with (44 + 5)%nat. rewrite (EL 5%nat ltac:(lia)). unfold LD. cbn [nth].
  pose proof (bv_unsigned_in_range 64 (ew E1 49)) as Hr. change (bv_modulus 64) with (2 ^ 64) in Hr.
  apply bv_eq. rewrite (fsw_reg_off (w_H W') E1 cae_exit_ss ms1 21%bv 49 0 (bv_unsigned (ew E1 49)) HS
                         ltac:(vm_compute; reflexivity) eq_refl ltac:(lia)).
  rewrite Z.add_0_r. reflexivity.
Qed.

(* ================= check_as_written_spec ================= *)
Theorem check_as_written_proof : @check_as_written_spec fx rc SK tfibsegs B.
Proof.
intros ly S U W regs mem md ch t bd l tb live peak cnt fail HPRE FH H10 H11 H12 Hcs Hck Hlen HANS HG Hev Hlv.
change (SRr tfibsegs W (cfg_at tfibsegs A_check_as_written regs mem md)
          (@cawb_post fx rc SK B regs ly S U W mem md live peak cnt fail)).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HSTK : 64 <= STK_check_as_written) by (change STK_check_as_written with 16448; lia).
assert (Hsp64 : 0 <= spZ regs < 2 ^ 64).
{ unfold spZ. pose proof (bv_unsigned_in_range 64 (getr regs 2)) as X. change (bv_modulus 64) with (2 ^ 64) in X.
  exact X. }
apply (@caw_front fx rc SK B IMG SYMS RTs RTm FS_ENV ML ly S U W regs mem md ch t bd l tb live peak cnt fail _
         HPRE FH H10 H11 H12 Hcs Hck Hlen HANS HG Hev Hlv).
(* ===== (1) the text is not empty: the scan loop, then its two exits ===== *)
- intros W2 ly2 S2 E0 ms0 mdc0 want six HPOST Hne HS0 HA0 E030 E034 E011 E012 HENT E031 E032 HST H60.
  destruct HPOST as (Hwle & Hbl & Hfr & Hnev & Hw1 & Hw2 & Hs1 & Hs2 & HJ0 & HARU0 & FH2 & HCK2 & HG2 & HRO2
    & HMF0 & RAW0 & HWRW0 & Hdj6w & Hdjtw & Hfrw & Hfr6 & HAWRW).
  assert (Hfr6' : forall m, ~ In (six, m) (ablocks B ly S))
    by (intros m Hm; apply (Hfr6 m); apply in_or_app; left; exact Hm).
  pose proof HST as (Hnz & Hlen3 & Ht0 & Ht1 & Htsh & Hs0' & Hs1' & Hsz & Hssh & Hdts & Hce & Hsp1 & Hsp2 & Hsp3
    & Hawr6).
  pose proof HA0 as (A02 & A033 & A035 & A036 & A037 & A038 & A039 & A040 & A041).
  assert (Hin6 : In (six, cawf_six_size tb) (ablocks B ly2 S2))
    by (rewrite Hbl; apply in_or_app; right; left; reflexivity).
  assert (Hinw : In (want, cawf_want_size tb) (ablocks B ly2 S2))
    by (rewrite Hbl; apply in_or_app; left; apply in_or_app; right; left; reflexivity).
  assert (Hssz : 1 <= cawf_six_size tb) by (unfold cawf_six_size; lia).
  assert (Hwsz : 3 <= cawf_want_size tb).
  { unfold cawf_want_size, b64_alloc_bound. assert (0 <= Z.of_nat (length tb) / 4) by (apply Z.div_pos; lia). lia. }
  pose proof (caw_inapp_block ly2 S2 U W2 (ms_mem ms0) mdc0 six _ HARU0 Hin6 Hssz) as App6.
  pose proof (caw_inapp_block ly2 S2 U W2 (ms_mem ms0) mdc0 want _ HARU0 Hinw ltac:(lia)) as Appw.
  apply (@caw_scan_loop fx rc SK B W2 STK_check_as_written (spZ regs) [] ly S W (unpoison U mem) md [] ly2 S2 U 2
           t tb six (cawf_six_size tb) (spZ regs) 0%nat [] 0 E0 ms0 mdc0 _ HST Hne HS0 HA0 eq_refl (Forall_nil _)
           HMF0 H60 HJ0 HARU0).
  intros ms1 mdc1 HPS.
  destruct HPS as (E1 & j' & mf & pad' & HAG1 & E135 & E138 & E139 & Hj' & Hmf & HMATCH & HKF1 & HGR1
    & HMF1 & HJ1 & HARU1).
  change (skipn 0 tb) with tb in HMATCH.
  pose proof HMF1 as (HG81 & RAT1 & RA61 & HWR61).
  assert (E12 : ew E1 2 = Z_to_bv 64 (spZ regs)) by (rewrite (HAG1 2%nat ltac:(lia)); exact A02).
  assert (E132 : ew E1 32 = Z_to_bv 64 SHADOW_OFF) by (rewrite (HAG1 32%nat ltac:(lia)); exact E032).
  assert (E133 : ew E1 33 = Z_to_bv 64 six) by (rewrite (HAG1 33%nat ltac:(lia)); exact A033).
  assert (E134 : ew E1 34 = Z_to_bv 64 want) by (rewrite (HAG1 34%nat ltac:(lia)); exact E034).
  assert (Esp1 : bv_unsigned (ew E1 2) = spZ regs) by (rewrite E12; apply unsigned_lit_small; lia).
  revert HMATCH. destruct (WriterSpec.b64_scan 0 [] tb) as [[sxf padf]|] eqn:HSCAN; intros HMATCH;
    cbv beta iota in HMATCH.
  2: {
    (* ===== the scan refused the character at j' (b64_dec = None): 0x81a78 with s5 = SIZE_MAX,
       caw_rekey_break ===== *)
    destruct HMATCH as (HS1 & Hjlt & Hnz' & Hmfj).
    destruct (@caw_rekey_break fx W2 E1 ms1 HS1) as (E2 & HAG2 & HS2 & E249).
    apply (caw_back ly S U W regs mem md ch bd l tb live peak cnt fail W2 ly2 S2 want six E2 ms1 mdc1
             SIZE_MAXZ HPRE FH H11 H12 Hlen HANS HG Hev Hbl Hfrw Hfr6' HS2).
    - intros k Hk. rewrite (proj1 HAG2 k ltac:(lia)), (HAG1 k ltac:(lia)). exact (HENT k Hk).
    - rewrite (proj1 HAG2 33%nat ltac:(lia)). exact E133.
    - rewrite (proj1 HAG2 34%nat ltac:(lia)). exact E134.
    - exact E249.
    - exact HJ1.
    - exact HARU1.
    - intros _. reflexivity.
    - intros bs Hd. rewrite (caw_dec_none_scan tb HSCAN) in Hd. discriminate. }
  (* ===== the scan reached the NUL with (sxf, padf): caw_rekey_tail, then the tail's five arms ===== *)
  destruct HMATCH as (HS1 & Hj'e & Hmfe & Hpade & Hsx64 & H6f).
  pose proof (caw_scan_bound tb 0 [] sxf padf HSCAN) as (_ & Hp0 & Hsb). cbn [length] in Hsb.
  subst mf pad'.
  (* want's shadow and writability, carried across the scan (it writes only six[m] and the frame) *)
  assert (RAW1 : range_addressable (rd_of tfibsegs (mrestrict (w_H W2) (ms_mem ms1))) SHADOW_OFF want
                   (cawf_want_size tb)).
  { apply (caw_ra_keep2 W2 (ms_mem ms0) (ms_mem ms1) want (cawf_want_size tb) six
             (six + Z.of_nat (length sxf) + 1) (spZ regs - 64) (spZ regs) RAW0 HKF1).
    - destruct App6 as [_ [X|[X _]]]; [left | right]; unfold kLowShadowBeg, SHADOW_OFF, cawf_six_size in *; lia.
    - right. unfold kHighMemBeg in *. lia.
    - lia.
    - unfold CAW_CEIL. lia. }
  assert (HWRW1 : forall a, want <= a < want + cawf_want_size tb ->
                    writable_at tfibsegs (mrestrict (w_H W2) (ms_mem ms1)) a)
    by (intros a Ha; apply (wview_grows tfibsegs _ _ _ HGR1); apply HWRW0; exact Ha).
  assert (Hlast : 0 <= last sxf 0 <= 63).
  { destruct sxf as [|v sxr]; [cbn; lia|]. rewrite caa_last_nth.
    assert (Hin : In (nth (Nat.pred (length (v :: sxr))) (v :: sxr) 0) (v :: sxr)) by (apply nth_In; cbn [length]; lia).
    pose proof (proj1 (Forall_forall _ _) Hsx64 _ Hin) as X. cbv beta in X. lia. }
  pose proof (@caw_rekey_tail fx W2 E1 ms1 six (Z.of_nat (length sxf)) (last sxf 0) HS1 E133 E138
                ltac:(lia) Hs0' ltac:(unfold CAW_CEIL, cawf_six_size in *; lia) Hlast) as HS2.
  remember (cawr_env E1 (ms_regs ms1) (Z_to_bv 64 (six + Z.of_nat (length sxf))) (Z_to_bv 64 (last sxf 0)))
    as E2 eqn:HE2.
  assert (HE2o : forall k, cawr_P k = true -> ew E2 k = ew E1 k)
    by (intros k Hk; rewrite HE2; apply cawr_env_old; exact Hk).
  assert (Hold2 : forall k, (k < 40)%nat -> ew E2 k = ew E1 k) by (intros k Hk; apply HE2o, caw_rP_lt40, Hk).
  assert (E232 : ew E2 32 = Z_to_bv 64 SHADOW_OFF) by (rewrite (Hold2 32%nat ltac:(lia)); exact E132).
  assert (E233 : ew E2 33 = Z_to_bv 64 six) by (rewrite (Hold2 33%nat ltac:(lia)); exact E133).
  assert (E234 : ew E2 34 = Z_to_bv 64 want) by (rewrite (Hold2 34%nat ltac:(lia)); exact E134).
  assert (E238 : ew E2 38 = Z_to_bv 64 (Z.of_nat (length sxf))) by (rewrite (Hold2 38%nat ltac:(lia)); exact E138).
  assert (E239 : ew E2 39 = Z_to_bv 64 padf) by (rewrite (Hold2 39%nat ltac:(lia)); exact E139).
  assert (E243 : ew E2 43 = Z_to_bv 64 (last sxf 0)) by (rewrite HE2; apply cawr_env_43).
  assert (Esp2 : bv_unsigned (ew E2 2) = spZ regs) by (rewrite (Hold2 2%nat ltac:(lia)); exact Esp1).
  destruct (Z_le_gt_dec padf 2) as [Hp2|Hp3].
  2: {
    (* ===== more than two '=' (b64_dec = None): cawt_refuse_pad, then caa_mkexit ===== *)
    apply (@cawt_refuse_pad fx rc SK B _ E2 ms1 mdc1 STK_check_as_written (spZ regs) [] ly S W (unpoison U mem) md
             [] ly2 S2 U W2 2 padf HS2 HJ1 HARU1 E239 ltac:(lia) Esp2 HSTK).
    intros E3 ms3 mdc3 HAG3 HS3 HJ3 HARU3 _ _.
    destruct (@caa_mkexit fx W2 E3 E3 ms3 (cawt_ss_free 3 3145728) (SLit 1) (SOff 54 0) (SOff 55 0)
                18446744073709551615 HS3 eq_refl eq_refl ltac:(vm_compute; reflexivity) eq_refl
                ltac:(lia) (fun _ _ => eq_refl) eq_refl) as (E4 & HAG4 & HS4 & E449).
    apply (caw_back ly S U W regs mem md ch bd l tb live peak cnt fail W2 ly2 S2 want six E4 ms3 mdc3
             18446744073709551615 HPRE FH H11 H12 Hlen HANS HG Hev Hbl Hfrw Hfr6' HS4).
    - intros k Hk. rewrite (proj1 HAG4 k ltac:(lia)), (HAG3 k ltac:(lia)), (Hold2 k ltac:(lia)),
        (HAG1 k ltac:(lia)). exact (HENT k Hk).
    - rewrite (proj1 HAG4 33%nat ltac:(lia)), (HAG3 33%nat ltac:(lia)). exact E233.
    - rewrite (proj1 HAG4 34%nat ltac:(lia)), (HAG3 34%nat ltac:(lia)). exact E234.
    - exact E449.
    - exact HJ3.
    - exact HARU3.
    - intros _. reflexivity.
    - intros bs Hd. rewrite (caw_dec_pad tb sxf padf HSCAN ltac:(lia)) in Hd. discriminate. }
  destruct (WriterSpec.six_tail_ok sxf) eqn:HT.
  2: {
    (* ===== the sextet tail is wrong (b64_dec = None): caa_refuse_tail ===== *)
    assert (Hm1 : (1 <= length sxf)%nat).
    { destruct sxf as [|v sxr]; [vm_compute in HT; discriminate HT | cbn [length]; lia]. }
    apply (@caa_refuse_tail fx rc SK B _ E2 ms1 mdc1 STK_check_as_written (spZ regs) [] ly S W (unpoison U mem) md []
             ly2 S2 U W2 2 sxf six want (cawf_six_size tb) (cawf_want_size tb) (Z.of_nat (length sxf)) padf
             HS2 HJ1 HARU1 Esp2 HSTK E232 E233 E234 E238 E239 E243
             ltac:(lia) ltac:(lia) eq_refl Hsx64 H6f App6 ltac:(unfold cawf_six_size; lia) Appw RA61 RAW1
             ltac:(unfold cawf_six_size in *; lia) HT).
    intros E3 ms3 mdc3 HAG3 HS3 E349 HJ3 HARU3 _ _ _ _.
    apply (caw_back ly S U W regs mem md ch bd l tb live peak cnt fail W2 ly2 S2 want six E3 ms3 mdc3
             SIZE_MAXZ HPRE FH H11 H12 Hlen HANS HG Hev Hbl Hfrw Hfr6' HS3).
    - intros k Hk. rewrite (proj1 HAG3 k ltac:(lia)), (Hold2 k ltac:(lia)), (HAG1 k ltac:(lia)).
      exact (HENT k Hk).
    - rewrite (proj1 HAG3 33%nat ltac:(lia)). exact E233.
    - rewrite (proj1 HAG3 34%nat ltac:(lia)). exact E234.
    - exact E349.
    - exact HJ3.
    - exact HARU3.
    - intros _. reflexivity.
    - intros bs Hd. rewrite (caw_dec_tail tb sxf padf HSCAN HT) in Hd. discriminate. }
  destruct (Nat.eq_dec (length sxf) 0) as [Hl0|Hl1].
  * (* ===== accepted, no sextet (b64_dec = Some []): caa_accept_m0 ===== *)
    assert (Hsx0 : sxf = []) by (destruct sxf; [reflexivity | cbn [length] in Hl0; lia]).
    assert (E2380 : ew E2 38 = Z_to_bv 64 0) by (rewrite E238, Hl0; reflexivity).
    apply (@caa_accept_m0 fx rc SK B _ E2 ms1 mdc1 STK_check_as_written (spZ regs) [] ly S W (unpoison U mem) md []
             ly2 S2 U W2 2 six want (cawf_six_size tb) (cawf_want_size tb) padf HS2 HJ1 HARU1 Esp2 HSTK
             E233 E234 E2380 E239 ltac:(lia) App6 Appw RA61 RAW1).
    intros E3 ms3 mdc3 HAG3 HS3 E349 HJ3 HARU3 _ _ _ _.
    apply (caw_back ly S U W regs mem md ch bd l tb live peak cnt fail W2 ly2 S2 want six E3 ms3 mdc3
             0 HPRE FH H11 H12 Hlen HANS HG Hev Hbl Hfrw Hfr6' HS3).
    + intros k Hk. rewrite (proj1 HAG3 k ltac:(lia)), (Hold2 k ltac:(lia)), (HAG1 k ltac:(lia)).
      exact (HENT k Hk).
    + rewrite (proj1 HAG3 33%nat ltac:(lia)). exact E233.
    + rewrite (proj1 HAG3 34%nat ltac:(lia)). exact E234.
    + exact E349.
    + exact HJ3.
    + exact HARU3.
    + intros Hd. rewrite (caw_dec_some tb sxf padf HSCAN ltac:(lia) HT) in Hd. discriminate.
    + intros bs Hd. rewrite (caw_dec_some tb sxf padf HSCAN ltac:(lia) HT) in Hd. injection Hd as <-.
      rewrite Hsx0. split; [reflexivity|]. split.
      ** unfold b64_alloc_bound. cbn [WriterSpec.six_bytes length Z.of_nat].
        assert (0 <= Z.of_nat (length tb) / 4) by (apply Z.div_pos; lia). lia.
      ** intros i Hi. cbn [WriterSpec.six_bytes length] in Hi. lia.
  * (* ===== accepted with sextets (b64_dec = Some (six_bytes sxf)): caa_accept_emit, the emit loop, the exit
       re-key ===== *)
    pose proof HT as HTc. unfold WriterSpec.six_tail_ok in HTc. cbv zeta in HTc.
    apply andb_prop in HTc as [HTc _]. apply andb_prop in HTc as [HT1 _].
    apply negb_true_iff, Z.eqb_neq in HT1.
    assert (HSB : Z.of_nat (length (WriterSpec.six_bytes sxf)) <= b64_alloc_bound (Z.of_nat (length tb)))
      by (apply caw_sixb_bound; lia).
    assert (Hwm : 3 * (Z.of_nat (length sxf) / 4) + 3 <= cawf_want_size tb).
    { assert (Z.of_nat (length sxf) / 4 <= Z.of_nat (length tb) / 4) by (apply Z.div_le_mono; lia).
      unfold cawf_want_size, b64_alloc_bound. lia. }
    apply (@caa_accept_emit fx rc SK B _ E2 ms1 mdc1 STK_check_as_written (spZ regs) [] ly S W (unpoison U mem) md []
             ly2 S2 U W2 2 sxf six want (cawf_six_size tb) (cawf_want_size tb) (Z.of_nat (length sxf)) padf
             HS2 HJ1 HARU1 Esp2 HSTK E232 E233 E234 E238 E239 E243
             ltac:(lia) ltac:(lia) eq_refl Hsx64 H6f App6 ltac:(unfold cawf_six_size; lia) Appw Hwm Hdj6w
             RA61 RAW1 HWRW1 ltac:(unfold cawf_six_size in *; lia) HT).
    intros E3 ms3 mdc3 HAG3 HS3 E347 E348 E349 E350 E351 E3sx E366 HJ3 HARU3 HB63 HKF3 HGR3 RA63 RAW3 HWR3 HRG3.
    assert (E332 : ew E3 32 = Z_to_bv 64 SHADOW_OFF) by (rewrite (proj1 HAG3 32%nat ltac:(lia)); exact E232).
    assert (E333 : ew E3 33 = Z_to_bv 64 six) by (rewrite (proj1 HAG3 33%nat ltac:(lia)); exact E233).
    assert (E334 : ew E3 34 = Z_to_bv 64 want) by (rewrite (proj1 HAG3 34%nat ltac:(lia)); exact E234).
    assert (E338 : ew E3 38 = Z_to_bv 64 (Z.of_nat (length sxf)))
      by (rewrite (proj1 HAG3 38%nat ltac:(lia)); exact E238).
    apply (@caw_emit_loop fx rc SK B _ (length sxf) sxf [] E3 ms3 mdc3 STK_check_as_written (spZ regs) [] ly S W
             (unpoison U mem) md [] ly2 S2 U W2 2 six want (cawf_six_size tb) (cawf_want_size tb)
             (Z.of_nat (length sxf)) 0 0 (le_n _) HS3 HJ3 HARU3 E332 E333 E334 E338 E347 E348 E349 E350 E351
             E3sx E366 Hsx64 ltac:(lia) eq_refl ltac:(lia) eq_refl HT1 eq_refl ltac:(lia) App6 Appw
             ltac:(unfold cawf_six_size; lia) Hwm Hdj6w RA63 RAW3 HWR3 HAWRW HB63
             ltac:(intros i Hi; cbn [length] in Hi; lia)).
    intros E4 ms4 mdc4 HAG4 HS4 E449 HJ4 HARU4 HBw HKF4 HGR4 _ _.
    (* the frame region at the loop entry, re-keyed onto the loop exit's env *)
    assert (HRG4 : region_ok tfibsegs E4 (ms_mem (restrict (w_H W2) ms3)) caw_stk).
    { assert (HM3 : mem_ok tfibsegs E3 (ms_mem (restrict (w_H W2) ms3)) [caw_stk]).
      { split; [vm_compute; reflexivity|]. split.
        - apply Forall_cons; [exact HRG3 | apply Forall_nil].
        - cbn [pairwise_disjoint all_disjoint]. split; exact I. }
      assert (HAT : mem_atoms_lt 47 [caw_stk] = true) by (vm_compute; reflexivity).
      destruct (mem_ok_agree tfibsegs 47 E3 E4 (ms_mem (restrict (w_H W2) ms3)) [caw_stk] HAG4 HAT HM3)
        as (_ & HFr & _).
      exact (Forall_inv HFr). }
    assert (Esp4 : bv_unsigned (ew E4 2) = spZ regs)
      by (rewrite (proj1 HAG4 2%nat ltac:(lia)), (proj1 HAG3 2%nat ltac:(lia)); exact Esp2).
    destruct (caw_emit_exit_env W2 E4 ms3 ms4 (spZ regs) HS4 HRG4 Esp4
                ltac:(intros x Hx; apply HKF4; unfold cawf_want_size in *; lia) HGR4) as (E5 & HAG5 & HS5 & E549).
    apply (caw_back ly S U W regs mem md ch bd l tb live peak cnt fail W2 ly2 S2 want six E5 ms4 mdc4
             (0 + Z.of_nat (length (WriterSpec.six_bytes sxf))) HPRE FH H11 H12 Hlen HANS HG Hev Hbl Hfrw
             Hfr6' HS5).
    + intros k Hk. rewrite (proj1 HAG5 k ltac:(lia)), (proj1 HAG4 k ltac:(lia)), (proj1 HAG3 k ltac:(lia)),
        (Hold2 k ltac:(lia)), (HAG1 k ltac:(lia)). exact (HENT k Hk).
    + rewrite (proj1 HAG5 33%nat ltac:(lia)), (proj1 HAG4 33%nat ltac:(lia)). exact E333.
    + rewrite (proj1 HAG5 34%nat ltac:(lia)), (proj1 HAG4 34%nat ltac:(lia)). exact E334.
    + rewrite E549. exact E449.
    + exact HJ4.
    + exact HARU4.
    + intros Hd. rewrite (caw_dec_some tb sxf padf HSCAN ltac:(lia) HT) in Hd. discriminate.
    + intros bs Hd. rewrite (caw_dec_some tb sxf padf HSCAN ltac:(lia) HT) in Hd. injection Hd as <-.
      split; [lia|]. split; [lia|]. exact HBw.
(* ===== (2) the text is empty: the empty-text arm at 0x81810 (b64_dec [] = Some []) ===== *)
- intros W2 ly2 S2 E0 ms0 mdc0 want six HPOST Htb HS0 A02 A030 A033 A034 A038 A011 A012 HENT A031 A032.
  subst tb.
  destruct HPOST as (Hwle & Hbl & Hfr & Hnev & Hw1 & Hw2 & Hs1 & Hs2 & HJ0 & HARU0 & FH2 & HCK2 & HG2 & HRO2
    & HMF0 & RAW0 & HWRW0 & Hdj6w & Hdjtw & Hfrw & Hfr6 & HAWRW).
  assert (Hfr6' : forall m, ~ In (six, m) (ablocks B ly S))
    by (intros m Hm; apply (Hfr6 m); apply in_or_app; left; exact Hm).
  pose proof HMF0 as (_ & _ & RA60 & _).
  assert (Hin6 : In (six, cawf_six_size []) (ablocks B ly2 S2))
    by (rewrite Hbl; apply in_or_app; right; left; reflexivity).
  assert (Hinw : In (want, cawf_want_size []) (ablocks B ly2 S2))
    by (rewrite Hbl; apply in_or_app; left; apply in_or_app; right; left; reflexivity).
  pose proof (caw_inapp_block ly2 S2 U W2 (ms_mem ms0) mdc0 six _ HARU0 Hin6 ltac:(vm_compute; discriminate))
    as App6.
  pose proof (caw_inapp_block ly2 S2 U W2 (ms_mem ms0) mdc0 want _ HARU0 Hinw ltac:(vm_compute; discriminate))
    as Appw.
  assert (Esp0 : bv_unsigned (ew E0 2) = spZ regs) by (rewrite A02; apply unsigned_lit_small; lia).
  apply (@caw_empty_tail fx rc SK B _ E0 ms0 mdc0 STK_check_as_written (spZ regs) [] ly S W (unpoison U mem) md []
           ly2 S2 U W2 2 six want (cawf_six_size []) (cawf_want_size []) HS0 HJ0 HARU0 Esp0 HSTK A033 A034 A038
           App6 Appw RA60 RAW0).
  intros E2 ms2 mdc2 HAG2 HS2 E249 HJ2 HARU2 _ _ _ _.
  apply (caw_back ly S U W regs mem md ch bd l [] live peak cnt fail W2 ly2 S2 want six E2 ms2 mdc2 0
           HPRE FH H11 H12 Hlen HANS HG Hev Hbl Hfrw Hfr6' HS2).
  + intros k Hk. rewrite (proj1 HAG2 k ltac:(lia)). exact (HENT k Hk).
  + rewrite (proj1 HAG2 33%nat ltac:(lia)). exact A033.
  + rewrite (proj1 HAG2 34%nat ltac:(lia)). exact A034.
  + exact E249.
  + exact HJ2.
  + exact HARU2.
  + intros Hd. vm_compute in Hd. discriminate.
  + intros bs Hd. vm_compute in Hd. injection Hd as <-. split; [reflexivity|]. split.
    * unfold b64_alloc_bound. cbn [length Z.of_nat]. lia.
    * intros i Hi. cbn [length] in Hi. lia.
Qed.

End A.
