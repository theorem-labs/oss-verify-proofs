(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "div"; "lt"; "mul"; "of_nat"; "sub"; "modulo"; "@Corelib.Init.Datatypes"; "snd"; "prod"; "length"; "list"; "fst"; "pair"; "@Stdlib.Lists.List"; "In"; "fold_right"; "@Corelib.Init.Logic"; "and"; "eq"; "ex"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeGap"; "total"; "disjoint"; "zrange"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.GapCount.Gap"; "killed"; "killed_all"; "meets"; "qlo"; "whi"; "wlo"; "@Corelib.Lists.ListDef"; "map"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import FreeGap.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Section Gap.
  Variable top n : Z.
  Hypothesis Hn : 0 < n.

  Definition wlo (i : Z) : Z := ltac2:(tb__ "0|0|
S7Vtop;S5S2Vi;Z1A2Vn;A2A2").
  Definition whi (i : Z) : Z := ltac2:(tb__ "0|0|
S7Vtop;S5Vi;Vn;A2A2").

  Definition meets (e : Z * Z) (i : Z) : Prop := ltac2:(tb__ "0|1|
S11S4SdS0S0Ve;A3M0S1cVi;A1A2S4S1dVi;A1S2G0S9S0S0Ve;A3A2A2A2").

  Definition qlo (e : Z * Z) : Z := ltac2:(tb__ "0|0|
S3S7S7Vtop;SdS0S0Ve;A3A2S9S0S0Ve;A3A2Vn;A2").
  Definition killed (e : Z * Z) : list Z := ltac2:(tb__ "0|0|
S1eS0S0S0S2S1bVe;A1R1A2Lt;S17S2S3S9S0S0Ve;A3Vn;A2Z2A2A1A4").

  Lemma meets_killed : ltac2:(tb__ "0|0|
SaS0S0A2S0S1Z0S9S0S0R2A3A2S1aR3R2A2SfS0R3S18R4A1A3F_;F_;Fi;Fe;").
  Proof using Hn.
    intros [b len] i Hlen [H1 H2]. unfold killed, qlo, whi, wlo in *. cbn [fst snd] in *.
    apply in_map_iff. exists (i - (top - b - len) / n). split; [lia|]. apply In_zrange.
    set (q := (top - b - len) / n) in *.
    pose proof (Z.mul_div_le (top - b - len) n Hn) as D1.
    pose proof (Z.mul_succ_div_gt (top - b - len) n Hn) as D2.
    set (p := len / n) in *.
    pose proof (Z.mul_div_le len n Hn) as D3. pose proof (Z.mul_succ_div_gt len n Hn) as D4.
    split.
    -   nia.
    -   nia.
  Qed.

  Lemma length_killed : ltac2:(tb__ "0|0|
SaS0S0A2S1Z0S9S0S0R1A3A2S12S0S6SbS0S18R2A1A2A1S2S3S9S0S0R2A3Vn;A2Z2A2A3F_;Fe;").
  Proof using Hn.
    intros [b len] Hlen. unfold killed. cbn [snd]. rewrite length_map, length_zrange; [reflexivity|].
    pose proof (Z.div_pos len n Hlen Hn). lia.
  Qed.

  Definition killed_all (l : list (Z * Z)) : list Z := flat_map killed l.

  Lemma sum_div_le : ltac2:(tb__ "0|3|
ScSaS0S0A2M0A1G0SfG0R1R2A3S1Z0M1S9S0S0R2A3M2A2F_;Fe;S1S10S0G0G0S0S2S3G2Vn;A2R1A2Lacc;Le;G1R2A5S3S15R2A1Vn;A2A2F_;Fl;").
  Proof using Hn.
    induction l as [|e t IH]; intros Hl; cbn [fold_right].
    - unfold total. cbn. rewrite Z.div_0_l by lia. lia.
    - specialize (IH ltac:(intros x Hx; apply Hl; right; exact Hx)).
      pose proof (Hl e ltac:(left; reflexivity)) as He.
      change (total (e :: t)) with (snd e + total t).
      assert (Ht : 0 <= total t).
      { clear IH. induction t as [|x t' IHt]; [unfold total; cbn; lia|].
        change (total (x :: t')) with (snd x + total t'). pose proof (Hl x ltac:(right; left; reflexivity)).
        specialize (IHt ltac:(intros y Hy; apply Hl; destruct Hy as [<-|Hy]; [left; reflexivity | right; right; exact Hy])). lia. }

      assert (DA : snd e / n + total t / n <= (snd e + total t) / n).
      { apply Z.div_le_lower_bound; [lia|].
        pose proof (Z.mul_div_le (snd e) n Hn). pose proof (Z.mul_div_le (total t) n Hn). lia. }
      lia.
  Qed.

  Lemma length_killed_all : ltac2:(tb__ "0|1|
ScSaS0S0A2M0A1G0SfG0R1R2A3S1Z0S9S0S0R2A3A2F_;Fe;S1S6SbS0S19R2A1A2A1S2S3S15R2A1Vn;A2S5Z2S6SbG0R2A2A1A2A2A2F_;Fl;").
  Proof using Hn.
    intros l Hl.
    assert (E : Z.of_nat (length (killed_all l)) = fold_right (fun e acc => snd e / n + acc) 0 l + 2 * Z.of_nat (length l)).
    { induction l as [|e t IH]; [reflexivity|]. unfold killed_all in *. cbn [flat_map fold_right length].
      rewrite length_app, Nat2Z.inj_add, (length_killed e (Hl e ltac:(left; reflexivity))), IH by (intros x Hx; apply Hl; right; exact Hx). lia. }
    rewrite E. pose proof (sum_div_le l Hl). lia.
  Qed.

  Lemma killed_all_in : ltac2:(tb__ "0|1|
ScSaS0S0A2M0A1G0S0SfG0R2R3A3SfS0R2S18R3A1A3SfS0R3S19R5A1A3F_;F_;Fi;Fe;Fl;").
  Proof using . intros l e i He Hi. unfold killed_all. apply in_flat_map. exists e. auto. Qed.

  Theorem gap_by_count : ltac2:(tb__ "0|2|
ScSaS0S0A2M0A1S0G0SfG0R1R3A3S1Z0M1S9S0S0R2A3A2F_;Fe;S1G1R2A2S4S2S3S15R4A1Vn;A2S5Z2S6SbG0R4A2A1A2A2R3A2S13S0S0S11S11S1G1R1A2S4R1R5A2A2G0SfG0R1R7A3S14S1aR2R3A2A1F_;Fe;A2Li;A2F_;F_;F_;FM;Fl;").
  Proof using Hn.
    intros l M Hl HM Hlt.
    destruct (exists_free_index (killed_all l) M HM ltac:(pose proof (length_killed_all l Hl); lia)) as (i & Hi & Hni).
    exists i. split; [exact Hi|]. intros e He Hm. apply Hni. apply (killed_all_in l e i He). apply meets_killed; [exact (Hl e He) | exact Hm].
  Qed.

  Corollary gap_by_count_base : ltac2:(tb__ "0|2|
ScSaS0S0A2M0A1S0S0G0SfG0R1R4A3S1Z0M1S9S0S0R2A3A2F_;Fe;S1G1R3A2S4S2S3S15R5A1Vn;A2S5Z2S6SbG0R5A2A1A2A2R4A2S4G1R4A2S12S0S8Vtop;R5A2G1A3S12S0S8Vn;R6A2G1A3S13S0S0S11S1S7Vtop;S5R9Vn;A2A2R1A2S11S1S2R1Vn;A2Vtop;A2S11S12S0S8R1R8A2G1A3G0SfG0R1RbA3S16SeS0S0R3Vn;A4R2A2F_;Fe;A2A2A2La;A2F_;F_;F_;F_;F_;F_;Fpg;FM;Fl;").
  Proof using Hn.
    intros l M pg Hl HM Hlt Hpg Htop Hnpg.
    destruct (gap_by_count l M Hl HM Hlt) as (i & Hi & Hfree).
    exists (wlo i). unfold wlo. split; [nia|]. split; [nia|]. split.
    - rewrite <- Zminus_mod_idemp_l, <- Zminus_mod_idemp_r, Htop, <- Zmult_mod_idemp_r, Hnpg, Z.mul_0_r. reflexivity.
    - intros e He. specialize (Hfree e He). unfold meets, FreeGap.disjoint, whi, wlo in *. cbn [fst snd].
      destruct (Z_lt_dec (fst e) (top - i * n)); [|lia]. destruct (Z_lt_dec (top - (i + 1) * n) (fst e + snd e)); [exfalso; apply Hfree; split; assumption | lia].
  Qed.
End Gap.
