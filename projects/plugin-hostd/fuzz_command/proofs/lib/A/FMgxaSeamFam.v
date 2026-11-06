(* Copied from proofs/omx-clap-core/fuzz_manifest/lib/A/FMgxaSeamFam.v; relocated to plugin-hostd/fuzz_command.asan by the GXA address relocator (target fuzz_command.asan): module paths changed; 0 address numerals moved (address checker 0767e70e074a, predict mode, fm.asan -> fuzz_command.asan, symbol + offset; the relocator's table for this file). *)
(* Step 2 of the evt -> SRr seam at musl vfprintf: the FORMAT and the ARGUMENTS.

   The shared contract's family (FMsnprintfShared.v pf_family, refined in FMgxaSeamDef.v as
   pf_family_ro) states the format and the arguments over the harness's reader
   `aview tfibsegs H mem`: fmt_at for the format, words_at for the va_list words, pf_args_asan per
   argument and pf_args_slack for the word past each string.  The released GXA statement
   (lib/CJ/RL/GXA/G_vfprintf_snf.v:194 vfprintf_snf_a_stmt) asks instead, over the CJ store
   `cjstore H mem` at the image A_img:
     bytes_at img_segs m A (zb fmt), Forall (0 <= c < 256) fmt   the format, its NUL included
     va_area m VA slots                                           (G_pop_arg.v:456)
     GXI.args_ok Fp lo 0 CK 16 D dn m lo q lo slots args          (GX/G_printf_core_common.v:281)
     args_pf m slots args, inside vf_snf_guard                    (G_vfprintf_snf.v:90)
   This file gives each from the shared premises.

   args_ok_of_pf_args_asan takes two premises its first proposed statement did not have, each the weakest
   that makes it true:
   - every 64-bit argument (AU64 u) is a machine word, 0 <= u < 2^64: GXA's PA_ull asks
     `bv_unsigned slot = u`, and pf_arg_asan's `w = u` does not bound u; words read through words_at
     are words (au64_range_of_ws with AFl3.rdword_range; FMgxaSeam.sa_args_fit);
   - lo + 8 <= q, not lo <= q: GXA keeps each string off the 8-byte va_list cell at ap = lo, and the
     window (lo, q - lo) covers that cell only when it is at least 8 bytes long.

   The slack GXA asks past each string is the bytes from w + |s| + 1 up to str_end w s, which
   pf_arg_asan says are present (str_slack); its length is (- (w + |s| + 1)) mod 8 (slack_len_eq).
   args_pf's pf_rng for a string is built from FMgxaSeamShadow's addressable_of_view and
   app_mem_of_amem_range, not from its pf_rng_of_view: that lemma asks amem_range w (|s| + 1 + 8),
   one byte more than pf_args_slack gives when w + |s| = 7 mod 8 and the string ends 9 bytes below
   kLowMemEnd or kHighMemEnd; pf_rng itself reads only up to w + |s| + 7 (amem_str_tail). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK04 YK0i YK0s YK14 YK1b YK1a YK18 YP09 YG0n YG00 YG0a YG01 YG0f YG0v YG0d YA0n YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AB1v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.CJ.Lib Require Mem Cells Arr.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.CJ.Spec Require Prelim.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.CJ.RL.G Require G_fmt_fp_lib G_pop_arg.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.CJ.RL.GX Require Import Printf_model.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.CJ.RL.GX Require G_printf_core_common.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.CJ.RL.GXA Require AsanFacts G_vfprintf_snf.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import RT_IImgA.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtPFPf RtPFShared.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import FMgxaSeamBase FMgxaSeamPf FMgxaSeamDef FMgxaSeamShadow FMgxaSeamCells.
Import ListNotations.
Local Open Scope Z_scope.

Module GXI := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.CJ.RL.GX.G_printf_core_common.G_printf_iface.
Module GXV := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.CJ.RL.GXA.G_vfprintf_snf.

Local Ltac nope := let E := fresh "E" in intros E; discriminate E.

Section f. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.

(* ---- words ---- *)
Lemma uw64 : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (w64 z) = z.
Proof. intros z Hz. exact (Mem.wa_unsigned z Hz). Qed.

Lemma uw64_mod32 : forall z, bv_unsigned (w64 z) mod 2 ^ 32 = z mod 2 ^ 32.
Proof.
intros z. unfold w64. rewrite Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 64) with (2 ^ 64). Z.div_mod_to_equations. lia.
Qed.

(* ---- 1. GXA's zb is FMgxaSeamBase's zb8 ---- *)
Lemma zb_zb8 : forall l, G_fmt_fp_lib.zb l = zb8 l.
Proof. reflexivity. Qed.

(* ---- 2. the format's bytes, its NUL included ---- *)
Lemma fmt_bytes_of_fmt_at : forall H mem rs f fmt,
  fmt_at (aview tfibsegs H mem) rs f fmt -> f + Z.of_nat (length fmt) + 1 <= 2 ^ 64 ->
  Mem.bytes_at tfibsegs (cjstore H mem) f (zb8 (fmt ++ [0])).
Proof.
intros H mem rs f fmt (Hf & Hb & _) Hhi.
apply bytes_at_of_view; [lia | rewrite length_app; cbn [length]; lia |].
intros i Hi. rewrite length_app in Hi. cbn [length] in Hi.
rewrite (Hb (Z.of_nat i) ltac:(lia)), Nat2Z.id. reflexivity.
Qed.

(* ---- 3. a format the parser accepts is bytes ---- *)
Lemma pf_parse_bytes : forall n f ps, (length f <= n)%nat -> pf_parse f = Some ps ->
  Forall (fun c => 0 < c < 256) f.
Proof.
induction n as [|n IH]; intros f ps Hn.
- destruct f as [|b r]; [intros _; constructor | cbn in Hn; lia].
- destruct f as [|b r]; [intros _; constructor|]. cbn [length] in Hn.
  assert (T : forall r' (k : pf_piece) ps', (length r' <= n)%nat ->
            option_map (cons k) (pf_parse r') = Some ps' -> Forall (fun c => 0 < c < 256) r').
  { intros r' k ps' Hr' E. destruct (pf_parse r') as [p'|] eqn:E'; [|discriminate E].
    exact (IH r' p' Hr' E'). }
  cbn [pf_parse].
  destruct (Z.eqb_spec b 37) as [->|_].
  + destruct r as [|c r1]; [nope|]. cbn [length] in Hn.
    intros HP. constructor; [lia|]. revert HP.
    destruct (Z.eqb_spec c 100) as [->|_];
      [intros HP; constructor; [lia | exact (T r1 _ ps ltac:(lia) HP)]|].
    destruct (Z.eqb_spec c 99) as [->|_];
      [intros HP; constructor; [lia | exact (T r1 _ ps ltac:(lia) HP)]|].
    destruct (Z.eqb_spec c 115) as [->|_];
      [intros HP; constructor; [lia | exact (T r1 _ ps ltac:(lia) HP)]|].
    destruct (Z.eqb_spec c 48) as [->|_].
    { destruct r1 as [|c2 [|c3 r3]]; try nope. cbn [length] in Hn.
      destruct ((c2 =? 52) && (c3 =? 120)) eqn:E1.
      { apply andb_true_iff in E1 as [E2 E3]. apply Z.eqb_eq in E2, E3. subst c2 c3.
        intros HP. do 3 (constructor; [lia|]). exact (T r3 _ ps ltac:(lia) HP). }
      destruct ((c2 =? 50) && (c3 =? 120)) eqn:E4; [|nope].
      apply andb_true_iff in E4 as [E2 E3]. apply Z.eqb_eq in E2, E3. subst c2 c3.
      intros HP. do 3 (constructor; [lia|]). exact (T r3 _ ps ltac:(lia) HP). }
    destruct (Z.eqb_spec c 108) as [->|_].
    { destruct r1 as [|c2 [|c3 r3]]; try nope. cbn [length] in Hn.
      destruct ((c2 =? 108) && (c3 =? 117)) eqn:E1; [|nope].
      apply andb_true_iff in E1 as [E2 E3]. apply Z.eqb_eq in E2, E3. subst c2 c3.
      intros HP. do 3 (constructor; [lia|]). exact (T r3 _ ps ltac:(lia) HP). }
    destruct (Z.eqb_spec c 46) as [->|_]; [|nope].
    destruct r1 as [|c2 [|c3 r3]]; try nope. cbn [length] in Hn.
    destruct ((c2 =? 42) && (c3 =? 115)) eqn:E1; [|nope].
    apply andb_true_iff in E1 as [E2 E3]. apply Z.eqb_eq in E2, E3. subst c2 c3.
    intros HP. do 3 (constructor; [lia|]). exact (T r3 _ ps ltac:(lia) HP).
  + destruct ((0 <? b) && (b <? 256)) eqn:Eb; [|nope].
    apply andb_true_iff in Eb as [E1 E2]. apply Z.ltb_lt in E1, E2.
    intros HP. constructor; [lia | exact (T r _ ps ltac:(lia) HP)].
Qed.

Lemma fmt_bytes_small : forall rd rs f fmt ps,
  fmt_at rd rs f fmt -> pf_parse fmt = Some ps -> Forall (fun c => 0 <= c < 256) (fmt ++ [0]).
Proof.
intros rd rs f fmt ps _ HP. apply Forall_app. split.
- eapply Forall_impl; [| exact (pf_parse_bytes (length fmt) fmt ps (le_n _) HP)].
  cbv beta. intros c Hc. lia.
- constructor; [lia | constructor].
Qed.

(* ---- 4. the va_list words ---- *)
Lemma va_area_of_words_at : forall H mem ap ws,
  0 <= ap -> ap + 8 * Z.of_nat (length ws) <= 2 ^ 64 ->
  words_at (aview tfibsegs H mem) ap ws -> @G_pop_arg.va_area A_img (cjstore H mem) ap (map w64 ws).
Proof.
intros H mem ap ws. revert ap. unfold G_pop_arg.va_area.
induction ws as [|v ws IH]; intros ap Hap Hhi Hw.
- cbn [map Arr.u64s]. apply Mem.bytes_at_nil. lia.
- cbn [map Arr.u64s]. cbn [length] in Hhi.
  apply (proj2 (Mem.bytes_at_app _ _ _ _ _)). split.
  + exact (bytes_of_rdword H mem ap v Hap ltac:(lia) (words_at_head _ _ _ _ Hw)).
  + rewrite Mem.length_le8. change (Z.of_nat 8) with 8.
    apply IH; [lia | lia | exact (words_at_tail _ _ _ _ Hw)].
Qed.

(* ---- 5. the arguments: GXI.args_ok ---- *)
(* the slack length GXA asks, (- (w + |s| + 1)) mod 8, is the distance to str_end *)
Lemma slack_len_eq : forall w s,
  (- (w + Z.of_nat (length s) + 1)) mod 8 = str_end w s - (w + Z.of_nat (length s) + 1).
Proof. intros w s. unfold str_end. Z.div_mod_to_equations. lia. Qed.

(* the bytes from w + |s| + 1 up to str_end w s, as the CJ store reads them *)
Definition str_slack (H : word -> bool) (mem : word -> option byte) (w : Z) (s : list Z) : list byte :=
  map (fun i => match Mem.mrd tfibsegs (cjstore H mem) (Mem.wa (w + Z.of_nat (length s) + 1 + Z.of_nat i)) with
                | Some b => b | None => Z_to_bv 8 0 end)
      (seq 0 (Z.to_nat (str_end w s - (w + Z.of_nat (length s) + 1)))).

Lemma str_slack_length : forall H mem w s,
  Z.of_nat (length (str_slack H mem w s)) = str_end w s - (w + Z.of_nat (length s) + 1).
Proof.
intros H mem w s. unfold str_slack. rewrite length_map, length_seq, Z2Nat.id; [reflexivity|].
unfold str_end. Z.div_mod_to_equations. lia.
Qed.

(* the string, its NUL and the slack are the store's bytes *)
Lemma str_bytes_of_view : forall H mem w s,
  0 <= w -> str_end w s <= 2 ^ 64 ->
  (forall i, 0 <= i <= Z.of_nat (length s) ->
     aview tfibsegs H mem (w + i) = Some (nth (Z.to_nat i) (s ++ [0]) 0)) ->
  (forall x, w + Z.of_nat (length s) < x < str_end w s -> aview tfibsegs H mem x <> None) ->
  Mem.bytes_at tfibsegs (cjstore H mem) w (G_fmt_fp_lib.zb s ++ Z_to_bv 8 0 :: str_slack H mem w s).
Proof.
intros H mem w s Hw Hhi Hb Hsk.
pose proof (str_slack_length H mem w s) as Hk.
assert (Hs8 : w + Z.of_nat (length s) + 1 <= str_end w s)
  by (unfold str_end; Z.div_mod_to_equations; lia).
replace (G_fmt_fp_lib.zb s ++ Z_to_bv 8 0 :: str_slack H mem w s)
  with (zb8 (s ++ [0]) ++ str_slack H mem w s)
  by (unfold zb8, G_fmt_fp_lib.zb; rewrite map_app, <- app_assoc; reflexivity).
apply (proj2 (Mem.bytes_at_app _ _ _ _ _)). split.
- apply bytes_at_of_view; [exact Hw | rewrite length_app; cbn [length]; lia |].
  intros i Hi. rewrite length_app in Hi. cbn [length] in Hi.
  rewrite (Hb (Z.of_nat i) ltac:(lia)), Nat2Z.id. reflexivity.
- rewrite zb8_length, length_app. cbn [length].
  split; [lia|]. split; [lia|]. intros i Hi.
  unfold str_slack. rewrite nth_error_map.
  rewrite (nth_error_nth' (seq 0 _) 0%nat) by (rewrite length_seq; lia).
  rewrite seq_nth by lia. cbn [option_map Nat.add].
  replace (w + Z.of_nat (length s + 1) + Z.of_nat i)
    with (w + Z.of_nat (length s) + 1 + Z.of_nat i) by lia.
  destruct (Mem.mrd tfibsegs (cjstore H mem) (Mem.wa (w + Z.of_nat (length s) + 1 + Z.of_nat i)))
    as [b|] eqn:E; [reflexivity|].
  exfalso. apply (Hsk (w + Z.of_nat (length s) + 1 + Z.of_nat i)); [lia|].
  rewrite aview_mrd, E. reflexivity.
Qed.

(* pf_args_slack's range ends at str_end, which is 8-aligned like kLowMemEnd and kHighMemEnd, so it
   covers the 7 bytes past the string's last byte *)
Lemma amem_str_tail : forall w s, 0 <= w -> amem_range w (str_end w s - w) ->
  amem_range w (Z.of_nat (length s) + 8).
Proof.
intros w s Hw Hr. unfold amem_range, str_end, kLowMemEnd, kHighMemBeg, kHighMemEnd in *.
Z.div_mod_to_equations. lia.
Qed.

Lemma str_word : forall w s, 0 <= w -> amem_range w (str_end w s - w) -> 0 <= w < 2 ^ 64.
Proof.
intros w s Hw Hr. pose proof (amem_str_tail w s Hw Hr) as Ht.
unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Ht. lia.
Qed.

Lemma str_end_bound : forall w s, amem_range w (str_end w s - w) -> str_end w s <= 2 ^ 64.
Proof. intros w s Hr. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hr. lia. Qed.

(* what the seam's statement needs to name a 64-bit argument as a word *)
Lemma au64_range_of_ws : forall rd rs ws args,
  pf_args_asan rd rs ws args -> Forall (fun w => 0 <= w < 2 ^ 64) ws ->
  forall u, In (AU64 u) args -> 0 <= u < 2 ^ 64.
Proof.
intros rd rs ws args. revert ws.
induction args as [|a args IH]; intros ws HA HW u Hu; [destruct Hu|].
destruct ws as [|w ws]; [destruct HA|].
destruct HA as [Ha HA]. apply Forall_cons_iff in HW as [Hw HW].
destruct Hu as [->|Hu]; [cbn [pf_arg_asan] in Ha; subst w; exact Hw|].
exact (IH ws HA HW u Hu).
Qed.

(* the rs shape is RtPFShared.vfp_out K sp s0 w fp cp with lo = sp - K, q = sp, RE = s0,
   RES = w, Fp = fp, RC = cp, RCS = 16 *)
Lemma args_ok_of_pf_args_asan :
  forall H mem (rs : list (Z * Z)) ws args (Fp Bb BS RC RCS RE RES lo q apr : Z),
    pf_args_asan (aview tfibsegs H mem) rs ws args ->
    pf_args_slack ws args ->
    (forall u, In (AU64 u) args -> 0 <= u < 2 ^ 64) ->
    rs = [(lo, q - lo); (RE, RES); (Fp, 232); (RC, RCS)] ->
    Bb = lo -> BS = 0 -> apr = lo -> lo + 8 <= q ->
    @GXI.args_ok A_img Fp Bb BS RC RCS RE RES (cjstore H mem) lo q apr (map w64 ws) (map pt_parg args).
Proof.
intros H mem rs ws args Fp Bb BS RC RCS RE RES lo q apr HA HS HU -> -> -> -> Hq.
(* GXI.args_ok and GXV.args_pf recurse structurally on the slots, so the slots go first *)
revert ws HA HS HU. induction args as [|a args IH]; intros ws HA HS HU;
  destruct ws as [|w ws]; [exact I | exact I | destruct HA |].
destruct HA as [Ha HA].
assert (HS' : pf_args_slack ws args) by (destruct a; [exact HS | exact HS | exact (proj2 HS)]).
assert (HU' : forall u, In (AU64 u) args -> 0 <= u < 2 ^ 64) by (intros u Hu; apply HU; right; exact Hu).
cbn [map GXI.args_ok]. split; [|exact (IH ws HA HS' HU')].
destruct a as [v|u|s]; cbn [pt_parg GXI.arg_ok].
- destruct Ha as [Hv Hm]. split; [exact Hv|]. rewrite uw64_mod32. exact Hm.
- cbn [pf_arg_asan] in Ha. subst w. apply uw64, HU. left. reflexivity.
- destruct HS as [Hsl _].
  destruct Ha as (Hs & Hw & _ & Hb & Hsk & Hd & _ & _ & _).
  pose proof (str_word w s ltac:(lia) Hsl) as Hw64.
  pose proof (str_end_bound w s Hsl) as Hend.
  pose proof (str_slack_length H mem w s) as Hk.
  apply Forall_cons_iff in Hd as [D1 Hd]. apply Forall_cons_iff in Hd as [D2 Hd].
  apply Forall_cons_iff in Hd as [D3 Hd]. apply Forall_cons_iff in Hd as [D4 _].
  unfold zdisjoint in D1, D2, D3, D4. cbn [fst snd] in D1, D2, D3, D4.
  exists (str_slack H mem w s). rewrite (uw64 w Hw64). unfold Prelim.zlength.
  rewrite Hk, slack_len_eq.
  split; [exact (str_bytes_of_view H mem w s ltac:(lia) Hend Hb Hsk)|].
  split; [exact Hs|].
  repeat split; lia.
Qed.

(* ---- 6. the arguments: args_pf ---- *)
Lemma pf_rng_of_str : forall H mem w s,
  0 <= w -> Z.of_nat (length s) + 8 < 2 ^ 31 -> amem_range w (str_end w s - w) ->
  range_addressable (aview tfibsegs H mem) SHADOW_OFF w (Z.of_nat (length s) + 1) ->
  @AsanFacts.pf_rng A_img (cjstore H mem) w (Z.of_nat (length s) + 1).
Proof.
intros H mem w s Hw Hl Hr HRA.
pose proof (amem_str_tail w s Hw Hr) as Ht.
assert (H1 : amem_range w (Z.of_nat (length s) + 1)) by (unfold amem_range in *; lia).
unfold AsanFacts.pf_rng, AsanFacts.end_in_app.
split; [lia|]. split; [exact (addressable_of_view H mem w (Z.of_nat (length s) + 1) Hw ltac:(lia) H1 HRA)|]. split.
- right. exact (app_mem_of_amem_range w (Z.of_nat (length s) + 8) (w + (Z.of_nat (length s) + 1)) Ht Hw ltac:(lia) ltac:(lia)).
- intros i Hi. exact (app_mem_of_amem_range w (Z.of_nat (length s) + 8) (w + i + 7) Ht Hw ltac:(lia) ltac:(lia)).
Qed.

Lemma args_pf_of_pf_args_asan : forall H mem rs ws args,
  pf_args_asan (aview tfibsegs H mem) rs ws args -> pf_args_slack ws args ->
  @GXV.args_pf A_img (cjstore H mem) (map w64 ws) (map pt_parg args).
Proof.
intros H mem rs ws args. revert ws.
induction args as [|a args IH]; intros ws HA HS;
  destruct ws as [|w ws]; [exact I | exact I | destruct HA |].
destruct HA as [Ha HA].
assert (HS' : pf_args_slack ws args) by (destruct a; [exact HS | exact HS | exact (proj2 HS)]).
cbn [map GXV.args_pf]. split; [|exact (IH ws HA HS')].
destruct a as [v|u|s]; cbn [pt_parg]; [exact I | exact I|].
destruct HS as [Hsl _].
destruct Ha as (_ & Hw & Hl & _ & _ & _ & _ & HRA & _).
rewrite (uw64 w (str_word w s ltac:(lia) Hsl)).
exact (pf_rng_of_str H mem w s ltac:(lia) Hl Hsl HRA).
Qed.

End f.
