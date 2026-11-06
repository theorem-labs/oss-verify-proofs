(* Copied from proofs/omx-clap-core/fuzz_manifest/lib/A/RT_pf_llu.v (a working branch 0ddf65fd8cc); relocated to libreac/fuzz_disco.asan by reloc.py (target disco-A): module paths changed; 1 address numerals moved (port_addr_check 0767e70e074a predict, fm.asan -> fuzz_disco.asan, symbol + offset; table: this file's rows in provenance/evidence/g9-gxa/g9tool/g9-table-disco-A.tsv); YImgTop zify_pre_hook added after the last Require. *)
(* Row R-llu of the printf seam widening R-1: the %llu conversion (Pllu) at ASan's printf_common.
   - THE ARM pcom_pcx_arm Pllu (RT_pf_sh.v): printf_common's scan reads "%llu" (FMpfStep.v pf_code Pllu) in one step
     as no flag, width or precision, the length "ll" and the conversion 'u' (I_pcxgram.v pcx_conv true 117 = PK_long),
     takes the one argument pf_step consumes, a 64-bit word, as PA_u u (RT_pf_sh.pa_of), and gives it the coverage
     None (RT_pf_sh.pc_cin1 Pllu). On the machine this is pcx_len_ll_spec (I_pcxdir.v) then pcx_ck_int_spec at
     lm = 108 (I_pcxchk.v): the argument pointer moves 8 bytes on, the slot is not loaded and no memory range is
     checked.
   - the NON-VACUITY control: for every piece predicate PK that covers Pllu, the format "%llu" at 0x10000 with the
     word 2^64 - 1, at a concrete reader, is inside FF_pcomK PK (RT_pf_sh.v), its argument fits (FMpfStep.v
     pf_arg_fit), and the scan accepts it with RT_pf_sh.pc_cinK as its coverage. Every part is closed by
     computation; nothing in the witness is abstract. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Bz Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YG0d YG0f YG0n YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A Require Import AF0x.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require Import PfFacts SnShared.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A Require Import FMpfStep.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A Require RT_pf_sh.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Bz.A Require Import I_pcxgram.
#[local] Ltac Zify.zify_pre_hook ::= try unfold YImgTop.IMG_TOP, YImgTop.IMG_LO in *.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Open Scope Z_scope.

Module RTS := OSSVerify.Proofs.libreac.fuzz_disco.lib.A.RT_pf_sh.

(* ---- the arm ---- *)
Lemma pcom_pcx_arm_llu : RTS.pcom_pcx_arm Pllu.
Proof.
  intros fuel rest args c a' C _ H. destruct args as [|[v|u|s] a'']; cbn [pf_step] in H; try discriminate H.
  injection H as <- <-. split.
  - intros n W. exists (S n).
    assert (E : pcx_walk (S fuel) (pf_code Pllu ++ rest) (map RTS.pa_of (AU64 u :: a''))
                = option_map S (pcx_walk fuel rest (map RTS.pa_of a''))) by reflexivity.
    rewrite E, W. reflexivity.
  - reflexivity.
Qed.

(* ---- the NON-VACUITY control ---- *)
(* "%llu" in fm's .rodata range, with the largest word as its argument *)
Definition llu_f : Z := 0x10000.
Definition llu_fmt : list Z := pf_code Pllu.
Definition llu_w : Z := 2 ^ 64 - 1.
(* "18446744073709551615" *)
Definition llu_T : list Z := [49; 56; 52; 52; 54; 55; 52; 52; 48; 55; 51; 55; 48; 57; 53; 53; 49; 54; 49; 53].
(* a reader with the format and its NUL at llu_f, and their shadow granule: the 8 shadow bytes at
   SHADOW_OFF + llu_f / 8 = 0x7fffa000 read 0 (addressable) *)
Definition llu_rd : reader := fun a =>
  if (0x7fffa000 <=? a) && (a <? 0x7fffa008) then Some 0
  else if (llu_f <=? a) && (a <=? llu_f + 4) then Some (nth (Z.to_nat (a - llu_f)) (llu_fmt ++ [0]) 0)
  else None.

Lemma llu_fmt_at : fmt_at llu_rd [] llu_f llu_fmt.
Proof.
  unfold fmt_at. change (Z.of_nat (length llu_fmt)) with 4.
  split; [unfold llu_f; lia|].
  split.
  { intros i Hi. assert (Hc : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4) by lia.
    destruct Hc as [-> | [-> | [-> | [-> | ->]]]]; vm_compute; reflexivity. }
  split; [constructor|].
  split; [unfold amem_range, YG0f.kLowMemEnd, llu_f; left; lia|].
  split.
  { intros x Hx. exists 0. split; [|left; reflexivity]. unfold llu_f in Hx.
    assert (Hc : x = 65536 \/ x = 65537 \/ x = 65538 \/ x = 65539 \/ x = 65540) by lia.
    destruct Hc as [-> | [-> | [-> | [-> | ->]]]]; vm_compute; reflexivity. }
  intros s Hs.
  lazymatch type of Hs with ?lo <= _ < ?hi =>
    let l := eval vm_compute in lo in let h := eval vm_compute in hi in change lo with l in Hs; change hi with h in Hs end.
  cbv beta delta [llu_rd].
  destruct ((0x7fffa000 <=? s) && (s <? 0x7fffa008)) eqn:B; [discriminate|].
  apply andb_false_iff in B as [B|B]; [apply Z.leb_gt in B | apply Z.ltb_ge in B]; exfalso; lia.
Qed.

(* inside FF_pcomK PK for every PK that covers Pllu, with a fitting argument *)
Theorem llu_control_family : forall PK : pf_piece -> Prop, PK Pllu ->
  RTS.FF_pcomK PK llu_rd [] llu_f [llu_w] llu_T /\ Forall pf_arg_fit [AU64 llu_w].
Proof.
  intros PK HK.
  split; [|constructor; [cbn [pf_arg_fit]; unfold llu_w; split; [apply Z.leb_le | apply Z.ltb_lt]; reflexivity | constructor]].
  unfold RTS.FF_pcomK. exists llu_fmt, [Pllu], [AU64 llu_w].
  split; [exact llu_fmt_at|].
  split; [cbv [llu_fmt pf_code]; discriminate|].
  split; [assert (E : TFIB_IMG_END = 0x5fe000) by (vm_compute; reflexivity); rewrite E;
          change (Z.of_nat (length llu_fmt)) with 4; unfold llu_f; lia|].
  split; [vm_compute; reflexivity|].
  split; [constructor; [exact HK | constructor]|].
  split; [split; [exact (eq_refl llu_w) | exact I]|].
  split; [exact I|].
  split; [vm_compute; reflexivity | exact I].
Qed.

(* the scan on it: accepted, with RT_pf_sh.pc_cinK as its coverage *)
Theorem llu_control_pcom :
  pcomx_ok (llu_fmt ++ [0]) (map RTS.pa_of [AU64 llu_w]) = true /\
  pcx_covs (length (llu_fmt ++ [0])) (llu_fmt ++ [0]) (map RTS.pa_of [AU64 llu_w]) (RTS.pc_cinK [Pllu])
    = RTS.pc_cinK [Pllu].
Proof. split; vm_compute; reflexivity. Qed.
