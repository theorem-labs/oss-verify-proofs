(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the program walk of rec_canonical on the ASan build of
   plugin-hostd/fuzz_command, in the shape of cgif_file_fuzzer's walks (lib/A/AC8b.v: a loop walked by the
   symbolic executor over the position-abstract listing, its inline shadow checks removed by tok_load/tok_branch)
   and of this unit's xstrdup walk (the malloc call through amalloc04_sub of PaCall.v).
   The walk is cut at six points: the malloc return (0x89338: the null check, decided by the executor, and the
   empty-line check), the outer head (0x89354), the word-scan head (0x89364), the word start (0x893a0), the copy
   head (0x893e8) and the tail (0x89474); the model of the output is lib/Prog/RecFacts.v's
   canon T = join_sp (words T), and the word lemmas below are the Words section of fuzz_command's own released
   plain proof lib/Prog/rec_canonical.v, copied so that the walk stands on RecFacts alone. The walk's hypotheses are
   the statement's AMALLOC4 and TL (CmdPaLib.v: the malloc trampoline is the rule's entry, the GOT shadow cell). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/rec_canonical.v, with its module paths and module names changed; 696 of its 835 lines of code are new or changed and 2224 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/U/Prog/CF/rec_canonical.v, with its module paths, module names, addresses and numbers changed; 520 of its 641 lines of code are new or changed and 714 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/U/Prog/CF/reply.v, with its module paths and module names changed; 399 of its 442 lines of code are new or changed and 598 lines of the source are left out. *)
(* B twin (fm.asan-ubsan, pin ca61e5c9eabc0050) of lib/A/FMstrstr.v at a working branch b6bc009d623, relocated A->B by Theorem Labs tools over the unstripped twins; every image numeral re-derived by symbol / section (a Theorem Labs lane reloc report). *)
(* fm's strstr runtime contract in the donor's form: astrstr_realizes PC_strstr (lib/A/FMH_Rt.v), the strstr
   interceptor (trampoline 0x4133c -> __interceptor_strstr 0x429bc -> musl strstr 0x93294 -> StrstrCheck 0x42a98)
   called inside fm's user-poison window (lv2_locate.c:98), over Poison's ARU.

   The walk is FMss_strstr_wrap.strstr_wrap_holds: a Theorem Labs lane's strstr_wrap (lib/A/Prog/strstr_wrap.v) re-run against
   the local-shadow statements FMss_*.v, because the copied walk asks for `shadow_rw m` (every shadow byte readable),
   which a donor call site never gives (the donor keeps the shadow lazy, YG0n.v:300-302, :323; YK04.v:519-523).
   This file adds no walk: it RUNS the walk on the cleaned store (A/FMbz_clean.v lib_run_clean: the donor gives no
   `mem_inv`, so the walk runs where it holds and the result transfers), meets the walk's premises from
   ecall_preU_k / cstr_ok / rom_viewN / rom_viewO / AR, and reads its post back through FMbz_clean.clean_window as
   rt_post_roU (FMrt_lift.rt_post_roU_win). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YK11 YK0s YK15 YK18 YP09 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YC20 YI00 YI04 YI16 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YK0i YK14.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.ReusableB Require Import YB1v YF0m YF0x.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMupoison.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMH_Base FMH_Rt FMrt_lift.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMbz_clean.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require FMspec_str.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Lib Require PropExec MState Mem Exec Frame Regs6ss RegisterBridge.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Img0 AsanRT.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require FMss_shv FMss_TwAsan FMss_strstr_wrap_c FMss_strstr_wrap.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B.Prog Require strstr_wrap_c asan_memcpy.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A.Spec Require StrStr.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B.Bz.A Require I_qck Shadow.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B.Bz.Lib Require Mem.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Module LM := OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Lib.Mem.
Module LF := OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Lib.Frame.
(* LE (lib/Lib Exec), R6 (Regs6ss), RB (RegisterBridge) come from FMrt_lift *)
Module LS := OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Lib.MState.
Module LP := OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Lib.PropExec.
Module IM := OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B.Img0.
Module ART := OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B.AsanRT.
Module SHV := OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B.FMss_shv.
Module TWA := OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B.FMss_TwAsan.
Module SSWc := OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B.FMss_strstr_wrap_c.
Module SSW := OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B.FMss_strstr_wrap.
Module SWc := OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B.Prog.strstr_wrap_c.
Module AMC := OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B.Prog.asan_memcpy.
Module SPS := OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B.FMspec_str.
Module SST := OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A.Spec.StrStr.
Module BzQ := OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B.Bz.A.I_qck.
Module BzS := OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B.Bz.A.Shadow.
Module BzM := OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B.Bz.Lib.Mem.

(* ---- image facts (computed on fm.asan's segment table) ---- *)

(* the eight bytes of __stack_chk_guard (0x5f50b0, .bss) read from the image whatever the store holds there *)
Lemma fm_guard_rom : forall j, 0 <= j < 8 -> exists b, LP.seg_rom IM.rsegs (LM.wa (SWc.GUARD + j)) = Some b.
Proof.
  intros j Hj. assert (Hc : j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/ j = 4 \/ j = 5 \/ j = 6 \/ j = 7) by lia.
  unfold SWc.GUARD.
  destruct Hc as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]]; vm_compute; eexists; reflexivity.
Qed.

Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.

(* ---- bytes: the donor's reader and lib/Lib's ---- *)

Lemma view_mrd : forall (H : word -> bool) mem a v,
  aview tfibsegs H mem a = Some v ->
  exists b, LM.mrd IM.rsegs (mrestrict H mem) (LM.wa a) = Some b /\ bv_unsigned b = v.
Proof.
  intros H mem a v E. unfold aview in E.
  destruct (mbyte tfibsegs (mrestrict H mem) a) as [b|] eqn:Eb; [|discriminate].
  cbn in E. injection E as <-. exists b. split; [exact Eb | reflexivity].
Qed.

Lemma view_some_mrd : forall (H : word -> bool) mem a, aview tfibsegs H mem a <> None ->
  exists b, LM.mrd IM.rsegs (mrestrict H mem) (LM.wa a) = Some b.
Proof.
  intros H mem a E. destruct (aview tfibsegs H mem a) as [v|] eqn:Ev; [|exfalso; exact (E eq_refl)].
  destruct (view_mrd H mem a v Ev) as (b & Eb & _). exists b. exact Eb.
Qed.

Lemma nth_le_bytes : forall n z k, (k < n)%nat ->
  nth_error (Z_to_le_bytes n z) k = Some (Z_to_bv 8 (Z.shiftr z (8 * Z.of_nat k))).
Proof.
  induction n as [|n IH]; intros z k Hk; [lia|].
  destruct k as [|k]; cbn [Z_to_le_bytes nth_error].
  - change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r. reflexivity.
  - rewrite IH by lia. rewrite Z.shiftr_shiftr by lia. f_equal. f_equal. f_equal. lia.
Qed.

(* w little-endian bytes the donor's reader sees are lib/Lib bytes *)
Lemma bytes_of_view : forall (H : word -> bool) (mem : word -> option byte) a (w : nat) v,
  0 <= a -> a + Z.of_nat w <= 2 ^ 64 -> 0 <= v < 2 ^ (8 * Z.of_nat w) ->
  (forall k, (k < w)%nat -> aview tfibsegs H mem (a + Z.of_nat k) = Some (le_byte v w k)) ->
  LM.bytes_at IM.rsegs (mrestrict H mem) a (Z_to_le_bytes w v).
Proof.
  intros H mem a w v Ha Hw Hv HK. split; [exact Ha|]. rewrite LM.length_Z_to_le_bytes. split; [exact Hw|].
  intros i Hi.
  destruct (view_mrd H mem _ _ (HK i Hi)) as (b & Eb & Ub). rewrite Eb, nth_le_bytes by exact Hi.
  f_equal. apply bv_eq. rewrite Z_to_bv_unsigned, Ub. unfold le_byte. rewrite (Z.mod_small v) by lia.
  unfold bv_wrap. change (bv_modulus 8) with 256. reflexivity.
Qed.

Lemma le_byte_1 : forall v, 0 <= v < 256 -> le_byte v 1 0 = v.
Proof.
  intros v Hv. unfold le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
  rewrite Z.shiftr_0_r. change (2 ^ 8) with 256. rewrite !Z.mod_small by lia. reflexivity.
Qed.

Lemma u8z : forall c, 0 <= c < 256 -> bv_unsigned (Z_to_bv 8 c) = c.
Proof. intros c Hc. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. apply Z.mod_small. lia. Qed.

Lemma map_u8 : forall l, Forall (fun c => 0 <= c < 256) l -> map bv_unsigned (map (Z_to_bv 8) l) = l.
Proof.
  induction l as [|c l IH]; intros F; [reflexivity|].
  apply Forall_cons_iff in F as [Fc Fl]. cbn [map]. rewrite u8z by exact Fc. rewrite IH by exact Fl. reflexivity.
Qed.

(* a C string (cstr) and its NUL are lib/Lib bytes *)
Lemma cstr_lib : forall (W : world tfibsegs) mem p l,
  cstr tfibsegs W mem p l -> 0 <= p -> p + Z.of_nat (length l) + 1 <= 2 ^ 64 ->
  LM.bytes_at IM.rsegs (mrestrict (w_H W) mem) p (map (Z_to_bv 8) l ++ [Z_to_bv 8 0])
  /\ Forall (fun c => 0 <= c < 256) l /\ ~ In (Z_to_bv 8 0) (map (Z_to_bv 8) l).
Proof.
  intros W mem p l (GA & NZ) Hp Hpl.
  assert (FR : Forall (fun c => 0 <= c < 256) l).
  { apply Forall_forall. intros c Hc. apply In_nth with (d := 0) in Hc as (j & Hj & <-).
    destruct (GA j ltac:(rewrite length_app; cbn [length]; lia)) as (_ & R). rewrite app_nth1 in R by exact Hj. exact R. }
  split; [|split; [exact FR|]].
  - split; [exact Hp|]. rewrite length_app, length_map. cbn [length]. split; [lia|].
    intros i Hi.
    destruct (GA i ltac:(rewrite length_app; cbn [length]; lia)) as (VM & R).
    specialize (VM 0%nat ltac:(lia)). rewrite Z.add_0_r in VM. rewrite le_byte_1 in VM by exact R.
    change (mbyte tfibsegs (mrestrict (w_H W) mem) (p + Z.of_nat i)) with (LM.mrd IM.rsegs (mrestrict (w_H W) mem) (LM.wa (p + Z.of_nat i))) in VM.
    rewrite VM. replace (map (Z_to_bv 8) l ++ [Z_to_bv 8 0]) with (map (Z_to_bv 8) (l ++ [0])) by (rewrite map_app; reflexivity).
    rewrite nth_error_map.
    rewrite (nth_error_nth' (l ++ [0]) 0) by (rewrite length_app; cbn [length]; lia). reflexivity.
  - intros Hin. apply in_map_iff in Hin as (c & Ec & Hc).
    pose proof (proj1 (Forall_forall _ _) FR c Hc) as Rc. pose proof (proj1 (Forall_forall _ _) NZ c Hc) as Nc.
    apply (f_equal (@bv_unsigned 8)) in Ec. rewrite u8z in Ec by exact Rc. rewrite u8z in Ec by lia. exact (Nc Ec).
Qed.

(* the bytes after a string's NUL up to its word's end (cstr_ok's last clause) *)
Lemma slack_lib : forall (H : word -> bool) mem e (k : nat), 0 <= e -> e + Z.of_nat k <= 2 ^ 64 ->
  (forall a, e <= a < e + Z.of_nat k -> aview tfibsegs H mem a <> None) ->
  exists hs, length hs = k /\ LM.bytes_at IM.rsegs (mrestrict H mem) e hs.
Proof.
  intros H mem e k He Hk HV. apply AMC.bytes_exist; [exact He | exact Hk |].
  intros j Hj. apply view_some_mrd. apply HV. lia.
Qed.

(* the interceptor's range check (AsanRT addressable) from the donor's range_addressable *)
Lemma addressable_of_view : forall (H : word -> bool) mem p n,
  0 <= p -> 0 <= n -> p + n <= ART.APPMEM_END -> (forall i, 0 <= i < n -> ART.app_mem (p + i)) ->
  range_addressable (aview tfibsegs H mem) SHADOW_OFF p n ->
  ART.addressable (mrestrict H mem) p n.
Proof.
  intros H mem p n Hp Hn Hpn Happ HRA. split; [exact Hp|]. split; [exact Hn|]. split; [exact Hpn|].
  intros i Hi. split; [exact (Happ i Hi)|].
  destruct (HRA (p + i) ltac:(lia)) as (s & Hs & Hok).
  destruct (view_mrd H mem _ _ Hs) as (b & Eb & Ub).
  exists b. split.
  - replace (ART.shadow_addr (p + i)) with (shadow_of_addr SHADOW_OFF (p + i))
      by (unfold ART.shadow_addr, shadow_of_addr, SHADOW_OFF, ART.ASAN_K; lia). exact Eb.
  - pose proof (bv_unsigned_in_range 8 b) as Rb. change (bv_modulus 8) with 256 in Rb.
    assert (Sb : bv_unsigned b < 128 -> bv_signed b = bv_unsigned b).
    { intros Hl. unfold bv_signed. apply bv_swrap_small. change (bv_half_modulus 8) with 128. lia. }
    unfold ART.shadow_ok. unfold saddr_ok in Hok. rewrite <- Ub in Hok.
    destruct Hok as [H0|[H1 H2]]; [left | right]; rewrite Sb by lia; lia.
Qed.

(* the walks' local shadow premise from the donor's shadow hull *)
Lemma shvis_of_hull : forall (H : word -> bool) mem p n,
  shadow_hull_vis (aview tfibsegs H mem) p n -> SHV.shvis (mrestrict H mem) p n.
Proof.
  intros H mem p n HV Hn s Hs. apply view_some_mrd. apply HV.
  assert (E1 : forall q, BzQ.al8 (BzS.shad q) = shadow_addr q / 8 * 8).
  { intros q. unfold BzQ.al8, BzS.shad, BzS.SHB, shadow_addr, SHADOW_OFF. rewrite (Z.add_comm (q / 8)). lia. }
  rewrite !E1 in Hs. exact Hs.
Qed.

(* an application byte range (amem_range) is lib/Lib app_mem byte by byte *)
Lemma app_of_amem : forall p n, 0 <= p -> amem_range p n -> forall i, 0 <= i < n -> ART.app_mem (p + i).
Proof.
  intros p n Hp HA i Hi. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in HA.
  unfold ART.app_mem, ART.LOWMEM_END, ART.HIGHMEM_BEG, ART.APPMEM_END. lia.
Qed.

(* the stack window ecall_preU_k gives, as lib/Lib's stk *)
Lemma stk_of_apresent_L : forall (H : word -> bool) mem lo hi, 0 <= lo -> hi <= 2 ^ 64 ->
  (forall a, lo <= a < hi -> apresent H mem a) -> LF.stk IM.rsegs (mrestrict H mem) lo hi.
Proof.
  intros H mem lo hi Hlo Hhi HP. split; [exact Hlo|]. split; [exact Hhi|].
  intros a Ha. destruct (HP a Ha) as (HH & b & Hb).
  assert (Em : mrestrict H mem (LM.wa a) = Some b) by (unfold mrestrict, LM.wa; rewrite HH; exact Hb).
  split.
  - unfold wview. rewrite Em. discriminate.
  - exists b. unfold LM.mrd. rewrite Em. reflexivity.
Qed.

Lemma wz64 : forall a, bv_unsigned (Z_to_bv 64 a) = a mod 2 ^ 64.
Proof. intros a. rewrite Z_to_bv_unsigned. reflexivity. Qed.

(* ---- the walk's premises on the cleaned store (A/FMbz_clean.v, a Theorem Labs lane's): lib/Lib's mrd, bytes_at and stk are
   the same definitions as lib/A/Bz's over the same image, so the Bz transfer lemmas read them directly ---- *)
Lemma mrd_cleanL : forall m (a : word), rom_eq m -> bv_unsigned a < 2 ^ 47 ->
  LM.mrd IM.rsegs (clean m) a = LM.mrd IM.rsegs m a.
Proof. intros m a HE Ha. exact (mrd_clean m a HE ltac:(unfold BzM.UTOP; lia)). Qed.

Lemma bytes_at_cleanL : forall m a bs, rom_eq m -> a + Z.of_nat (length bs) <= 2 ^ 47 ->
  LM.bytes_at IM.rsegs m a bs -> LM.bytes_at IM.rsegs (clean m) a bs.
Proof. intros m a bs HE Hu H. exact (bytes_at_clean m a bs HE ltac:(unfold BzM.UTOP; lia) H). Qed.

Lemma stk_cleanL : forall m lo hi, TFIB_IMG_END <= lo -> hi <= 2 ^ 47 ->
  LF.stk IM.rsegs m lo hi -> LF.stk IM.rsegs (clean m) lo hi.
Proof. intros m lo hi Hlo Hhi H. exact (stk_clean m lo hi Hlo ltac:(unfold BzM.UTOP; lia) H). Qed.

Lemma wa_lt47 : forall a, 0 <= a < 2 ^ 47 -> bv_unsigned (LM.wa a) < 2 ^ 47.
Proof. intros a Ha. rewrite LM.wa_unsigned by lia. lia. Qed.

(* the interceptor's range check reads only shadow bytes, all below 2^47 *)
Lemma addressable_cleanL : forall m p n, rom_eq m -> ART.addressable m p n -> ART.addressable (clean m) p n.
Proof.
  intros m p n HE (H0 & H1 & H2 & H). split; [exact H0|]. split; [exact H1|]. split; [exact H2|].
  intros i Hi. destruct (H i Hi) as (Happ & b & Hb & Hok). split; [exact Happ|].
  exists b. split; [| exact Hok]. rewrite mrd_cleanL; [exact Hb | exact HE |].
  apply wa_lt47. unfold ART.shadow_addr, ART.ASAN_K. unfold ART.APPMEM_END in H2.
  assert (0 <= (p + i) / 8 <= p + i) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia). lia.
Qed.

(* and so does the walks' local shadow premise *)
Lemma shvis_cleanL : forall m p n, rom_eq m -> 0 <= p -> p + n <= 2 ^ 47 -> SHV.shvis m p n -> SHV.shvis (clean m) p n.
Proof.
  intros m p n HE Hp Hpn H Hn s Hs. destruct (H Hn s Hs) as (b & Hb). exists b.
  rewrite mrd_cleanL; [exact Hb | exact HE |]. apply wa_lt47.
  unfold BzQ.al8, BzS.shad, BzS.SHB in Hs.
  assert (0 <= p / 8 <= p) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
  assert (0 <= (p + n - 1) / 8 <= p + n - 1) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
  Z.div_mod_to_equations. lia.
Qed.

(* ---- the runtime cells AR fixes (fm's Tfib_const, lib/A/YF0m.v) ---- *)

Definition ss_cells : list acell :=
  [ z8 (ANum 0x99c88) 0x133ba8; z8 (ANum 0x9b9c8) 0x93294; z8 (ANum 0x9b9d0) 0x92d9c; z8 (ANum 0x9b9e8) 0x92790;
    z8 (ANum 0x9b9d8) 0x9285c; z8 (ANum 0x133c98) 0x101000100000000; z8 (ANum 0x133ca0) 0x101010101010101;
    z8 (ANum 0x9a920) 0x5f50b0;
    z8 (ANum 0xa2078) 0x7fff8000; z8 (ANum 0x99c98) 0xa2078; z1 (ANum 0xa2d58) 0x1; z1 (ANum 0xa2d59) 0x1;
    z8 (ANum 0x9a800) 0xa2d59; z4 (ANum 0xa2080) 0x1; z8 (ANum 0x99cf0) 0xa2080; z1 (ANum 0xa18dc) 0x1;
    z8 (ANum 0xa2d60) 0x7fffffffffff; z8 (ANum 0x99cb0) 0xa2d60; z8 (ANum 0xa2d68) 0x0; z8 (ANum 0x99ca0) 0xa2d68;
    z8 (ANum 0xa2d70) 0x0; z8 (ANum 0x99ca8) 0xa2d70; z8 (ANum 0x9bb20) 0x9288c; z8 (ANum 0x9bb28) 0x92c90;
    z8 (ANum 0x99cb8) 0x9bb28 ].

Ltac in_ss := unfold ss_cells; cbn [In]; repeat (first [left; reflexivity | right]).

Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis TFS : TfibSyms B.

(* each of them is one of fm's constant cells (lib/A/YF0m.v Tfib_const_abs), which AR fixes *)
Lemma ss_cells_const : forall ly, Forall (fun c => In c (as_const B ly)) ss_cells.
Proof.
  intros ly. rewrite (ts_const B TFS ly). unfold Tfib_const.
  apply Forall_forall. intros c Hc. apply in_or_app. right. apply in_or_app. left.
  unfold ss_cells in Hc. cbn [In] in Hc.
  repeat (destruct Hc as [<- | Hc]; [unfold Tfib_const_abs; cbn [In]; repeat (first [left; reflexivity | right]) |]).
  destruct Hc.
Qed.

(* a constant cell below the shadow, read through ARU's memory, is a lib/Lib byte run of the walk's (cleaned) memory *)
Lemma cell_lib : forall ly S U W mem md a (w : nat) v,
  ARU tfibsegs B ly S U W mem md -> rom_eq (mrestrict (w_H W) mem) -> In (ACell (ANum a) w (AV (ANum v))) ss_cells ->
  0 <= a -> a + Z.of_nat w <= SHADOW_OFF -> 0 <= v < 2 ^ (8 * Z.of_nat w) ->
  LM.bytes_at IM.rsegs (clean (mrestrict (w_H W) mem)) a (Z_to_le_bytes w v).
Proof.
  intros ly S U W mem md a w v HARU HE Hin Ha Haw Hv.
  pose proof (proj1 (Forall_forall _ _) (ss_cells_const ly) _ Hin) as Hc.
  pose proof (am_const B ly S _ (proj1 (proj1 HARU))) as HC.
  pose proof (proj1 (Forall_forall _ _) HC _ Hc) as HH. unfold cell_holds in HH. cbn [c_at c_val c_w aeval] in HH.
  apply bytes_at_cleanL; [exact HE | rewrite LM.length_Z_to_le_bytes; unfold SHADOW_OFF in Haw; lia |].
  apply bytes_of_view; [exact Ha | unfold SHADOW_OFF in Haw; lia | exact Hv |].
  intros k Hk. rewrite <- (HH k Hk).
  apply aview_at. symmetry. eapply ARU_mem_low; [exact HARU|].
  rewrite wz64, Z.mod_small by (unfold SHADOW_OFF in Haw; lia). unfold SHADOW_OFF in *. lia.
Qed.

Lemma le8_wa : forall v, 0 <= v < 2 ^ 64 -> LM.le8 (LM.wa v) = Z_to_le_bytes 8 v.
Proof. intros v Hv. unfold LM.le8, word_to_le_bytes, LM.wa. rewrite LS.unsigned_lit by exact Hv. reflexivity. Qed.

Lemma le4_wa : forall v, 0 <= v < 2 ^ 32 -> LM.le4 (LM.wa v) = Z_to_le_bytes 4 v.
Proof. intros v Hv. unfold LM.le4, LM.wa. rewrite LS.unsigned_lit by lia. reflexivity. Qed.

Lemma cell8 : forall ly S U W mem md a v,
  ARU tfibsegs B ly S U W mem md -> rom_eq (mrestrict (w_H W) mem) -> In (z8 (ANum a) v) ss_cells -> 0 <= a ->
  a + 8 <= SHADOW_OFF -> 0 <= v < 2 ^ 64 ->
  LM.bytes_at IM.rsegs (clean (mrestrict (w_H W) mem)) a (LM.le8 (LM.wa v)).
Proof.
  intros ly S U W mem md a v H HE Hin Ha Haw Hv. rewrite le8_wa by exact Hv.
  exact (cell_lib ly S U W mem md a 8 v H HE Hin Ha Haw Hv).
Qed.

Lemma cell1 : forall ly S U W mem md a v,
  ARU tfibsegs B ly S U W mem md -> rom_eq (mrestrict (w_H W) mem) -> In (z1 (ANum a) v) ss_cells -> 0 <= a ->
  a + 1 <= SHADOW_OFF -> 0 <= v < 256 ->
  LM.bytes_at IM.rsegs (clean (mrestrict (w_H W) mem)) a [Z_to_bv 8 v].
Proof.
  intros ly S U W mem md a v H HE Hin Ha Haw Hv.
  exact (cell_lib ly S U W mem md a 1 v H HE Hin Ha Haw Hv).
Qed.

Lemma cell4 : forall ly S U W mem md a v,
  ARU tfibsegs B ly S U W mem md -> rom_eq (mrestrict (w_H W) mem) -> In (z4 (ANum a) v) ss_cells -> 0 <= a ->
  a + 4 <= SHADOW_OFF -> 0 <= v < 2 ^ 32 ->
  LM.bytes_at IM.rsegs (clean (mrestrict (w_H W) mem)) a (LM.le4 (LM.wa v)).
Proof.
  intros ly S U W mem md a v H HE Hin Ha Haw Hv. rewrite le4_wa by exact Hv.
  exact (cell_lib ly S U W mem md a 4 v H HE Hin Ha Haw Hv).
Qed.

(* one byte of an 8-byte constant cell *)
Lemma cell8_byte : forall ly S U W mem md a v k,
  ARU tfibsegs B ly S U W mem md -> rom_eq (mrestrict (w_H W) mem) -> In (z8 (ANum a) v) ss_cells -> 0 <= a ->
  a + 8 <= SHADOW_OFF -> (k < 8)%nat ->
  LM.bytes_at IM.rsegs (clean (mrestrict (w_H W) mem)) (a + Z.of_nat k) [Z_to_bv 8 (le_byte v 8 k)].
Proof.
  intros ly S U W mem md a v k HARU HE Hin Ha Haw Hk.
  pose proof (proj1 (Forall_forall _ _) (ss_cells_const ly) _ Hin) as Hc.
  pose proof (am_const B ly S _ (proj1 (proj1 HARU))) as HC.
  pose proof (proj1 (Forall_forall _ _) HC _ Hc) as HH. unfold cell_holds, z8, c8 in HH. cbn [c_at c_val c_w aeval] in HH.
  assert (E : aview tfibsegs (w_H W) mem (a + Z.of_nat k) = Some (le_byte v 8 k)).
  { rewrite <- (HH k Hk). apply aview_at. symmetry. eapply ARU_mem_low; [exact HARU|].
    rewrite wz64, Z.mod_small by (unfold SHADOW_OFF in Haw; lia). unfold SHADOW_OFF in *. lia. }
  destruct (view_mrd _ _ _ _ E) as (b & Eb & Ub).
  apply bytes_at_cleanL; [exact HE | cbn [length]; unfold SHADOW_OFF in Haw; lia |].
  split; [lia|]. split; [cbn [length]; unfold SHADOW_OFF in Haw; lia|].
  intros i Hi. cbn [length] in Hi. assert (Hi0 : i = 0%nat) by lia. subst i. cbn [nth_error]. rewrite Z.add_0_r, Eb.
  f_equal. apply bv_eq. rewrite Ub, u8z; [reflexivity|]. unfold le_byte. apply Z.mod_pos_bound. lia.
Qed.

Lemma asan_cells_of_AR : forall ly S U W mem md,
  ARU tfibsegs B ly S U W mem md -> rom_eq (mrestrict (w_H W) mem) ->
  ART.asan_cells (clean (mrestrict (w_H W) mem)).
Proof.
  intros ly S U W mem md H HE. unfold ART.asan_cells, ART.CELL_K, ART.ASAN_K, ART.GOT_CELL_K, ART.INITED, ART.REPLACE,
    ART.GOT_REPLACE, ART.UAR, ART.GOT_UAR, ART.CANPOISON, ART.HIEND, ART.GOT_HIEND, ART.MIDBEG, ART.GOT_MIDBEG,
    ART.MIDEND, ART.GOT_MIDEND, ART.REAL_MEMCPY, ART.REAL_MEMSET, ART.GOT_REAL_MEMSET, ART.MUSL_MEMCPY, ART.MUSL_MEMSET.
  repeat match goal with |- _ /\ _ => split end.
  all: first
    [ apply (cell8 ly S U W mem md); [exact H | exact HE | in_ss | unfold SHADOW_OFF; lia | unfold SHADOW_OFF; lia | lia]
    | apply (cell1 ly S U W mem md); [exact H | exact HE | in_ss | unfold SHADOW_OFF; lia | unfold SHADOW_OFF; lia | lia]
    | apply (cell4 ly S U W mem md); [exact H | exact HE | in_ss | unfold SHADOW_OFF; lia | unfold SHADOW_OFF; lia | lia] ].
Qed.

(* ---- the contract ---- *)

Theorem fm_astrstr : astrstr_realizes tfibsegs B PC_strstr.
Proof.
  unfold astrstr_realizes.
  intros ly S U W regs mem md x y lt lw PRE ROM SC Ex Ey CX CY.
  pose proof PRE as PRE0.
  destruct PRE as (((HAR & RET & SP16 & SPLO & SPHI & APR & GP & TP) & UOK & UPO) & CEIL & STKLO & APRK).
  assert (HARU : ARU tfibsegs B ly S U W mem md) by (split; [exact HAR | split; [exact UOK | exact UPO]]).
  pose proof (stk_kHighMemBeg B ly S _ (proj1 HAR)) as [SKB SKE].
  pose proof alloc_ceiling_lt as ACL. pose proof alloc_ceiling_value as [[ACV _] _].
  unfold STK_RT_STRSTR, ESTACK in STKLO, APRK.
  assert (SPR : 0 <= spZ regs < 2 ^ 64).
  { unfold spZ. pose proof (bv_unsigned_in_range 64 (getr regs 2)) as R. change (bv_modulus 64) with (2 ^ 64) in R. lia. }
  assert (SPE : bv_unsigned (getr regs 2) = spZ regs) by reflexivity.
  set (sp := spZ regs) in *.
  set (m := mrestrict (w_H W) mem).
  (* the donor gives no `mem_inv`, so the walk runs on the cleaned store (A/FMbz_clean.v lib_run_clean) *)
  assert (ROMEQ : rom_eq m) by exact (rom_eq_of_views B W mem TFS ROM SC).
  set (mc := clean m).
  (* the two strings *)
  destruct CX as (CSX & X4 & XC & XL & XAM & XRA & XHV & XSL).
  destruct CY as (CSY & Y4 & YC & YL & YAM & YRA & YHV & YSL).
  destruct (cstr_lib W mem x lt CSX ltac:(lia) ltac:(lia)) as (BX & FX & NZX).
  destruct (cstr_lib W mem y lw CSY ltac:(lia) ltac:(lia)) as (BY & FY & NZY).
  assert (HX : bv_unsigned (getr regs 10) = x) by (rewrite Ex; unfold w64; apply LS.unsigned_lit; lia).
  assert (HY : bv_unsigned (getr regs 11) = y) by (rewrite Ey; unfold w64; apply LS.unsigned_lit; lia).
  set (nx := Z.of_nat (length lt)) in *. set (ny := Z.of_nat (length lw)) in *.
  assert (NX : nx = Z.of_nat (length lt)) by reflexivity. assert (NY : ny = Z.of_nat (length lw)) by reflexivity.
  assert (Hnx : 0 <= nx) by lia. assert (Hny : 0 <= ny) by lia.
  set (hb := map (Z_to_bv 8) lt). set (nb := map (Z_to_bv 8) lw).
  assert (LHB : Z.of_nat (length hb) = nx) by (unfold hb; rewrite length_map; reflexivity).
  assert (LNB : Z.of_nat (length nb) = ny) by (unfold nb; rewrite length_map; reflexivity).
  assert (MH : map bv_unsigned hb = lt) by (unfold hb; apply map_u8; exact FX).
  assert (MN : map bv_unsigned nb = lw) by (unfold nb; apply map_u8; exact FY).
  set (ks := Z.to_nat ((- (x + nx + 1)) mod 8)).
  assert (KS : Z.of_nat ks = (- (x + nx + 1)) mod 8) by (unfold ks; rewrite Z2Nat.id; [reflexivity | apply Z.mod_pos_bound; lia]).
  destruct (slack_lib (w_H W) mem (x + nx + 1) ks ltac:(lia) ltac:(lia)) as (hs & LHS & BHS).
  { intros a Ha. apply XSL. rewrite KS in Ha. Z.div_mod_to_equations. lia. }
  (* the guard word *)
  destruct (AMC.bytes_exist mc 8 SWc.GUARD ltac:(unfold SWc.GUARD; lia) ltac:(unfold SWc.GUARD; lia)) as (gbs & GL & GB).
  { intros j Hj. change (Z.of_nat 8) with 8 in Hj. unfold LM.mrd.
    destruct (mc (LM.wa (SWc.GUARD + j))) as [b|]; [exists b; reflexivity|]. exact (fm_guard_rom j Hj). }
  set (g := Z_to_bv 64 (bytes_le_to_Z gbs)).
  (* the walk *)
  pose proof SSW.strstr_wrap_holds as K. unfold SSWc.strstr_wrap_contract in K.
  specialize (K (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4) (getr regs 5) (getr regs 6) (getr regs 7)
                (getr regs 8) (getr regs 9) (getr regs 10) (getr regs 11) (getr regs 12) (getr regs 13) (getr regs 14)
                (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18) (getr regs 19) (getr regs 20)
                (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26)
                (getr regs 27) (getr regs 28) (getr regs 29) (getr regs 30) (getr regs 31)
                fp_regs fp_csr mc hb hs nb (sp - 8192) g).
  cbv zeta in K. rewrite HX, HY in K. change (bv_unsigned (getr regs 2)) with sp in K. rewrite LHB, LNB in K.
  assert (WALK : LE.evt IM.rsegs
      (SSWc.strstr_wrap_post (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4) (getr regs 8) (getr regs 9)
         (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24)
         (getr regs 25) (getr regs 26) (getr regs 27) fp_regs fp_csr (getr regs 10) (getr regs 11) hb hs nb
         (sp - 8192) mc)
      (LS.MS (LF.mkR (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4) (getr regs 5) (getr regs 6) (getr regs 7)
                (getr regs 8) (getr regs 9) (getr regs 10) (getr regs 11) (getr regs 12) (getr regs 13) (getr regs 14)
                (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18) (getr regs 19) (getr regs 20)
                (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26)
                (getr regs 27) (getr regs 28) (getr regs 29) (getr regs 30) (getr regs 31))
          fp_regs (Z_to_bv 64 SWc.STRSTR_WRAP) fp_csr None mc (LP.seg_rom IM.rsegs))).
  { apply K.
    - (* haystack bytes, NUL, slack *)
      apply bytes_at_cleanL; [exact ROMEQ | rewrite length_app; cbn [length]; rewrite LHS;
        pose proof (Z.mod_pos_bound (- (x + nx + 1)) 8 ltac:(lia)); lia |].
      apply LM.bytes_at_app. apply LM.bytes_at_app in BX as [BX1 BX0]. split; [exact BX1|].
      change (Z_to_bv 8 0 :: hs) with ([Z_to_bv 8 0] ++ hs). apply LM.bytes_at_app. split; [exact BX0|].
      rewrite LHB. cbn [length]. replace (x + nx + Z.of_nat 1) with (x + nx + 1) by lia. exact BHS.
    - exact NZX.
    - rewrite LHS, KS. lia.
    - lia.
    - apply bytes_at_cleanL; [exact ROMEQ | rewrite length_app; cbn [length]; lia | exact BY].
    - exact NZY.
    - exact (AMC.mem_inv_of_bz mc (mem_inv_clean m)).
    - apply (cell8 ly S U W mem md SWc.GOT_GUARD SWc.GUARD HARU ROMEQ); [in_ss | unfold SWc.GOT_GUARD; lia
        | unfold SWc.GOT_GUARD, SHADOW_OFF; lia | unfold SWc.GUARD; lia].
    - unfold g. rewrite (AMC.le8_of_len8 gbs GL). exact GB.
    - lia.
    - lia.
    - apply (addressable_cleanL m _ _ ROMEQ). apply addressable_of_view; [lia | lia | unfold ART.APPMEM_END; lia | |].
      + intros i Hi. apply (app_of_amem x (nx + 8)); [lia | exact XAM | lia].
      + exact XRA.
    - apply (addressable_cleanL m _ _ ROMEQ). apply addressable_of_view; [lia | lia | unfold ART.APPMEM_END; lia | |].
      + intros i Hi. apply (app_of_amem y (ny + 8)); [lia | exact YAM | lia].
      + exact YRA.
    - right. apply (app_of_amem x (nx + 8)); [lia | exact XAM | lia].
    - right. apply (app_of_amem y (ny + 8)); [lia | exact YAM | lia].
    - intros i Hi. replace (x + i + 7) with (x + (i + 7)) by lia. apply (app_of_amem x (nx + 8)); [lia | exact XAM | lia].
    - intros i Hi. replace (y + i + 7) with (y + (i + 7)) by lia. apply (app_of_amem y (ny + 8)); [lia | exact YAM | lia].
    - left. unfold SWc.STRSTR_WRAP_K. rewrite LHS, KS. Z.div_mod_to_equations. lia.
    - left. unfold SWc.STRSTR_WRAP_K. lia.
    - assert (SL : TFIB_IMG_END <= sp - 8192) by (unfold TFIB_IMG_END; unfold kHighMemBeg in SKB; lia).
      assert (SH8 : sp <= 2 ^ 47) by (unfold kHighMemEnd in SKE; lia).
      apply (stk_cleanL m _ _ SL SH8). apply stk_of_apresent_L; [lia | lia |]. intros a Ha. apply APRK. lia.
    - unfold SWc.STRSTR_WRAP_K. lia.
    - unfold ART.HIGHMEM_BEG. lia.
    - unfold ART.APPMEM_END. unfold kHighMemEnd in SKE. lia.
    - exact (asan_cells_of_AR ly S U W mem md HARU ROMEQ).
    - unfold TWA.shv2. rewrite HX, HY, LHB, LNB.
      split; (apply (shvis_cleanL m); [exact ROMEQ | lia | lia | apply shvis_of_hull; assumption]).
    - apply (cell8 ly S U W mem md); [exact HARU | exact ROMEQ | in_ss | unfold SWc.REAL_STRSTR; lia | unfold SWc.REAL_STRSTR, SHADOW_OFF; lia | unfold SWc.STRSTR; lia].
    - apply (cell8 ly S U W mem md); [exact HARU | exact ROMEQ | in_ss | unfold SWc.REAL_STRCHR; lia | unfold SWc.REAL_STRCHR, SHADOW_OFF; lia | unfold SWc.STRCHR; lia].
    - apply (cell8 ly S U W mem md); [exact HARU | exact ROMEQ | in_ss | unfold SWc.REAL_MEMCHR; lia | unfold SWc.REAL_MEMCHR, SHADOW_OFF; lia | unfold OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B.Prog.memchr_c.MEMCHR; lia].
    - apply (cell8 ly S U W mem md); [exact HARU | exact ROMEQ | in_ss | unfold SWc.REAL_MEMCMP; lia | unfold SWc.REAL_MEMCMP, SHADOW_OFF; lia | unfold OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B.Prog.memcmp_c.MEMCMP; lia].
    - apply (cell8 ly S U W mem md); [exact HARU | exact ROMEQ | in_ss | unfold SWc.GOT_CF; lia | unfold SWc.GOT_CF, SHADOW_OFF; lia | unfold SWc.CF; lia].
    - replace (SWc.CF + 245) with (0x133c98 + Z.of_nat 5) by (unfold SWc.CF; lia).
      replace (Z_to_bv 8 0) with (Z_to_bv 8 (le_byte 0x101000100000000 8 5)) by (f_equal; vm_compute; reflexivity).
      apply (cell8_byte ly S U W mem md); [exact HARU | exact ROMEQ | in_ss | lia | unfold SHADOW_OFF; lia | lia].
    - replace (SWc.CF + 246) with (0x133c98 + Z.of_nat 6) by (unfold SWc.CF; lia).
      replace (Z_to_bv 8 1) with (Z_to_bv 8 (le_byte 0x101000100000000 8 6)) by (f_equal; vm_compute; reflexivity).
      apply (cell8_byte ly S U W mem md); [exact HARU | exact ROMEQ | in_ss | lia | unfold SHADOW_OFF; lia | lia].
    - replace (SWc.CF + 253) with (0x133ca0 + Z.of_nat 5) by (unfold SWc.CF; lia).
      replace (Z_to_bv 8 1) with (Z_to_bv 8 (le_byte 0x101010101010101 8 5)) by (f_equal; vm_compute; reflexivity).
      apply (cell8_byte ly S U W mem md); [exact HARU | exact ROMEQ | in_ss | lia | unfold SHADOW_OFF; lia | lia].
    - replace (SWc.CF + 254) with (0x133ca0 + Z.of_nat 6) by (unfold SWc.CF; lia).
      replace (Z_to_bv 8 1) with (Z_to_bv 8 (le_byte 0x101010101010101 8 6)) by (f_equal; vm_compute; reflexivity).
      apply (cell8_byte ly S U W mem md); [exact HARU | exact ROMEQ | in_ss | lia | unfold SHADOW_OFF; lia | lia].
    - replace (SWc.CF + 255) with (0x133ca0 + Z.of_nat 7) by (unfold SWc.CF; lia).
      replace (Z_to_bv 8 1) with (Z_to_bv 8 (le_byte 0x101010101010101 8 7)) by (f_equal; vm_compute; reflexivity).
      apply (cell8_byte ly S U W mem md); [exact HARU | exact ROMEQ | in_ss | lia | unfold SHADOW_OFF; lia | lia]. }
  (* the run, read at the donor call site through the cleaned store, and its post read back: the walk changed only
     its frame of the cleaned store and left that frame present, so the real store changed only that frame and left
     it present (A/FMbz_clean.v clean_window) *)
  eapply (lib_run_clean B TFS W PC_strstr regs mem md _ _ ROM SC); [exact WALK|].
  intros msc ms' model' HQ Hclc EQV SBM HCL.
  destruct HQ as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
                  E0 & MU & WM & MI & ST & AC & SH & BH' & BN').
  assert (EM : ms_mem msc = m') by (rewrite E0; reflexivity).
  assert (MOUT : forall w : word, ~ (sp - 4608 <= bv_unsigned w < sp) -> ms_mem msc w = clean m w).
  { intros w Hw. rewrite EM. apply MU. cbn [LF.outside]. split; [|exact I].
    rewrite SPE. unfold SWc.STRSTR_WRAP_K. lia. }
  assert (MIN : forall a, sp - 4608 <= a < sp -> ms_mem msc (Z_to_bv 64 a) <> None).
  { intros a Ha E. rewrite EM in E.
    destruct ST as (_ & _ & STA). rewrite SPE in STA. destruct (STA a ltac:(lia)) as (_ & b & Hb).
    unfold LM.mrd, LM.wa in Hb. rewrite E in Hb.
    pose proof (seg_rom_none_high a ltac:(unfold TFIB_IMG_END; lia)) as N.
    change (seg_rom tfibsegs (Z_to_bv 64 a)) with (LP.seg_rom IM.rsegs (Z_to_bv 64 a)) in N.
    rewrite N in Hb. discriminate. }
  destruct (clean_window m msc (sp - 4608) sp Hclc MOUT MIN) as (CW1 & CW2).
  subst msc.
  pose proof (SPS.strstr_val_spec x hb nb) as VS. rewrite MH, MN in VS.
  eapply (rt_post_roU_win B LAWS STK_RT_STRSTR 4608 ly S U W regs mem md _ _ ms' model' (SST.strstr_val x hb nb)).
  - exact PRE0.
  - unfold STK_RT_STRSTR, ESTACK. lia.
  - exact EQV.
  - exact SBM.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - unfold unrestrict. cbn [ms_regs LS.MS]. keep_regs.
  - unfold unrestrict. cbn [ms_regs LS.MS]. rewrite HX. reflexivity.
  - destruct VS as [(V0 & _) | (j & ((OL & _) & _) & Vj)]; [rewrite V0; lia|].
    rewrite Vj. lia.
  - exact VS.
  - exact CW1.
  - exact CW2.
Qed.

End s.
