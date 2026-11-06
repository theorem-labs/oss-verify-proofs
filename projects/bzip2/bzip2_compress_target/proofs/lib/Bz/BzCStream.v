(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArr.
Import ListNotations.
Open Scope Z_scope.
From Stdlib Require Lia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition crc32_table : list Z :=
  [
   0; 79764919; 159529838; 222504665; 319059676; 398814059; 445009330; 507990021;
   638119352; 583659535; 797628118; 726387553; 890018660; 835552979; 1015980042; 944750013;
   1276238704; 1221641927; 1167319070; 1095957929; 1595256236; 1540665371; 1452775106; 1381403509;
   1780037320; 1859660671; 1671105958; 1733955601; 2031960084; 2111593891; 1889500026; 1952343757;
   2552477408; 2632100695; 2443283854; 2506133561; 2334638140; 2414271883; 2191915858; 2254759653;
   3190512472; 3135915759; 3081330742; 3009969537; 2905550212; 2850959411; 2762807018; 2691435357;
   3560074640; 3505614887; 3719321342; 3648080713; 3342211916; 3287746299; 3467911202; 3396681109;
   4063920168; 4143685023; 4223187782; 4286162673; 3779000052; 3858754371; 3904687514; 3967668269;
   881225847; 809987520; 1023691545; 969234094; 662832811; 591600412; 771767749; 717299826;
   311336399; 374308984; 453813921; 533576470; 25881363; 88864420; 134795389; 214552010;
   2023205639; 2086057648; 1897238633; 1976864222; 1804852699; 1867694188; 1645340341; 1724971778;
   1587496639; 1516133128; 1461550545; 1406951526; 1302016099; 1230646740; 1142491917; 1087903418;
   2896545431; 2825181984; 2770861561; 2716262478; 3215044683; 3143675388; 3055782693; 3001194130;
   2326604591; 2389456536; 2200899649; 2280525302; 2578013683; 2640855108; 2418763421; 2498394922;
   3769900519; 3832873040; 3912640137; 3992402750; 4088425275; 4151408268; 4197601365; 4277358050;
   3334271071; 3263032808; 3476998961; 3422541446; 3585640067; 3514407732; 3694837229; 3640369242;
   1762451694; 1842216281; 1619975040; 1682949687; 2047383090; 2127137669; 1938468188; 2001449195;
   1325665622; 1271206113; 1183200824; 1111960463; 1543535498; 1489069629; 1434599652; 1363369299;
   622672798; 568075817; 748617968; 677256519; 907627842; 853037301; 1067152940; 995781531;
   51762726; 131386257; 177728840; 240578815; 269590778; 349224269; 429104020; 491947555;
   4046411278; 4126034873; 4172115296; 4234965207; 3794477266; 3874110821; 3953728444; 4016571915;
   3609705398; 3555108353; 3735388376; 3664026991; 3290680682; 3236090077; 3449943556; 3378572211;
   3174993278; 3120533705; 3032266256; 2961025959; 2923101090; 2868635157; 2813903052; 2742672763;
   2604032198; 2683796849; 2461293480; 2524268063; 2284983834; 2364738477; 2175806836; 2238787779;
   1569362073; 1498123566; 1409854455; 1355396672; 1317987909; 1246755826; 1192025387; 1137557660;
   2072149281; 2135122070; 1912620623; 1992383480; 1753615357; 1816598090; 1627664531; 1707420964;
   295390185; 358241886; 404320391; 483945776; 43990325; 106832002; 186451547; 266083308;
   932423249; 861060070; 1041341759; 986742920; 613929101; 542559546; 756411363; 701822548;
   3316196985; 3244833742; 3425377559; 3370778784; 3601682597; 3530312978; 3744426955; 3689838204;
   3819031489; 3881883254; 3928223919; 4007849240; 4037393693; 4100235434; 4180117107; 4259748804;
   2310601993; 2373574846; 2151335527; 2231098320; 2596047829; 2659030626; 2470359227; 2550115596;
   2947551409; 2876312838; 2788305887; 2733848168; 3165939309; 3094707162; 3040238851; 2985771188 ].

Definition crc32_tbl (i : Z) : Z := nth (Z.to_nat i) crc32_table 0.

(* [comment removed for export] *)
Definition crc_update (crc cha : Z) : Z :=
  Z.lxor ((Z.shiftl crc 8) mod 4294967296) (crc32_tbl (Z.lxor (Z.shiftr crc 24) (Z.land cha 255))).
(* [comment removed for export] *)
Definition crc_init : Z := 4294967295.
Definition crc_final (crc : Z) : Z := Z.lxor crc 4294967295.

(* [comment removed for export] *)
Fixpoint crc_update_n (crc ch : Z) (n : nat) : Z :=
  match n with
  | O => crc
  | S n' => crc_update_n (crc_update crc ch) ch n'
  end.
Lemma crc_update_n_S : forall crc ch n, crc_update_n crc ch (S n) = crc_update_n (crc_update crc ch) ch n.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Record bw := BW { bw_buff : Z; bw_live : Z; bw_numZ : Z; bw_zb : zarr }.
Definition bw_bytes (b : bw) : list Z := zarr_to_list (bw_zb b) 0 (Z.to_nat (bw_numZ b)).

(* [comment removed for export] *)
Definition bw_emit (b : bw) : bw :=
  BW ((Z.shiftl (bw_buff b) 8) mod 4294967296) (bw_live b - 8) (bw_numZ b + 1)
     (zset (bw_zb b) (bw_numZ b) (Z.shiftr (bw_buff b) 24)).

(* [comment removed for export] *)
Fixpoint bs_needw (fuel : nat) (b : bw) : bw :=
  match fuel with
  | O => b
  | S f => if 8 <=? bw_live b then bs_needw f (bw_emit b) else b
  end.
Definition BS_FUEL : nat := 5%nat.

(* [comment removed for export] *)
Definition bsW (b : bw) (n v : Z) : bw :=
  let b1 := bs_needw BS_FUEL b in
  BW (Z.lor (bw_buff b1) ((Z.shiftl v (32 - bw_live b1 - n)) mod 4294967296)) (bw_live b1 + n) (bw_numZ b1) (bw_zb b1).

(* [comment removed for export] *)
Fixpoint bs_finish (fuel : nat) (b : bw) : bw :=
  match fuel with
  | O => b
  | S f => if 0 <? bw_live b then bs_finish f (bw_emit b) else b
  end.

(* [comment removed for export] *)
Definition bsPutUInt32 (b : bw) (u : Z) : bw :=
  let b := bsW b 8 (Z.land (Z.shiftr u 24) 255) in
  let b := bsW b 8 (Z.land (Z.shiftr u 16) 255) in
  let b := bsW b 8 (Z.land (Z.shiftr u 8) 255) in
  bsW b 8 (Z.land u 255).
Definition bsPutUChar (b : bw) (c : Z) : bw := bsW b 8 c.

Lemma bs_needw_S : forall f b, bs_needw (S f) b = (if 8 <=? bw_live b then bs_needw f (bw_emit b) else b).
Proof. reflexivity. Qed.
Lemma bs_finish_S : forall f b, bs_finish (S f) b = (if 0 <? bw_live b then bs_finish f (bw_emit b) else b).
Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Record rlst := RL {
  rl_nblock : Z;
  rl_block : zarr;
  rl_inUse : zarr;
  rl_crc : Z;          (* [comment removed for export] *)
  rl_ch : Z;           (* [comment removed for export] *)
  rl_len : Z           (* [comment removed for export] *)
}.

(* [comment removed for export] *)
Definition rl_put (r : rlst) (b : Z) : rlst :=
  RL (rl_nblock r + 1) (zset (rl_block r) (rl_nblock r) (Z.land b 255)) (rl_inUse r) (rl_crc r) (rl_ch r) (rl_len r).

(* [comment removed for export] *)
Definition add_pair_to_block (r : rlst) : rlst :=
  let ch := Z.land (rl_ch r) 255 in
  let crc := crc_update_n (rl_crc r) ch (Z.to_nat (rl_len r)) in
  let r1 := RL (rl_nblock r) (rl_block r) (zset (rl_inUse r) (rl_ch r) 1) crc (rl_ch r) (rl_len r) in
  let n := rl_len r in
  if n =? 1 then rl_put r1 ch
  else if n =? 2 then rl_put (rl_put r1 ch) ch
  else if n =? 3 then rl_put (rl_put (rl_put r1 ch) ch) ch
  else
    let r2 := RL (rl_nblock r1) (rl_block r1) (zset (rl_inUse r1) (n - 4) 1) (rl_crc r1) (rl_ch r1) (rl_len r1) in
    rl_put (rl_put (rl_put (rl_put (rl_put r2 ch) ch) ch) ch) (n - 4).

(* [comment removed for export] *)
Definition init_RL (r : rlst) : rlst := RL (rl_nblock r) (rl_block r) (rl_inUse r) (rl_crc r) 256 0.

(* [comment removed for export] *)
Definition flush_RL (r : rlst) : rlst :=
  init_RL (if rl_ch r <? 256 then add_pair_to_block r else r).

(* [comment removed for export] *)
Definition isempty_RL (r : rlst) : bool := negb ((rl_ch r <? 256) && (0 <? rl_len r)).

(* [comment removed for export] *)
Definition add_char_to_block (r : rlst) (zchh : Z) : rlst :=
  if negb (zchh =? rl_ch r) && (rl_len r =? 1) then
    (* [comment removed for export] *)
    let ch := Z.land (rl_ch r) 255 in
    let crc := crc_update (rl_crc r) ch in
    RL (rl_nblock r + 1) (zset (rl_block r) (rl_nblock r) ch) (zset (rl_inUse r) (rl_ch r) 1) crc zchh (rl_len r)
  else if negb (zchh =? rl_ch r) || (rl_len r =? 255) then
    let r1 := if rl_ch r <? 256 then add_pair_to_block r else r in
    RL (rl_nblock r1) (rl_block r1) (rl_inUse r1) (rl_crc r1) zchh 1
  else
    RL (rl_nblock r) (rl_block r) (rl_inUse r) (rl_crc r) (rl_ch r) (rl_len r + 1).

(* [comment removed for export] *)
Fixpoint inUse_clear (a : zarr) (i : Z) (n : nat) : zarr :=
  match n with
  | O => a
  | S n' => inUse_clear (zset a i 0) (i + 1) n'
  end.
Lemma inUse_clear_S : forall a i n, inUse_clear a i (S n) = inUse_clear (zset a i 0) (i + 1) n.
Proof. reflexivity. Qed.
Definition prepare_new_block_rl (r : rlst) : rlst :=
  RL 0 (rl_block r) (inUse_clear (rl_inUse r) 0 256) crc_init (rl_ch r) (rl_len r).
