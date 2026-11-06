(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YO08.v, with its module paths changed. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YO07.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Definition raw_attr_of (attr : Z) : Z := (if YO07.flag attr 2 then 1 else 0) + (if YO07.flag attr 16 then 2 else 0).
Definition gs_new (W H attr ngp loops : Z) (GPAL : list Z) : YO07.gif_st :=
YO07.mkS None None None 1 YO07.C_PENDING YO07.R_PENDING
[YO07.raw_header W H (if YO07.flag attr 4 then 0 else ngp) GPAL (raw_attr_of attr) loops].
Definition hdr5 (payload : list Z) : bool * (Z * Z * Z * Z * Z) * list Z :=
let '(e1, w, s1) := YO07.rd payload 2 in let '(e2, h, s2) := YO07.rd s1 2 in let '(e3, a, s3) := YO07.rd s2 4 in
let '(e4, ge, s4) := YO07.rd s3 4 in let '(e5, n, s5) := YO07.rd s4 2 in
(e1 || e2 || e3 || e4 || e5, (YO07.le_bytes w, YO07.le_bytes h, YO07.le_bytes a, YO07.le_bytes ge, YO07.le_bytes n), s5).
Definition ff_cfg (payload : list Z) : option (YO07.gcfg * Z * list Z) :=
let '(e, hd, s5) := hdr5 payload in let '(W, H, attr, gen, ngp) := hd in
let '(e6, gpal, s6) := if YO07.flag attr 4 then (false, [], s5) else YO07.rd s5 (ngp * 3) in
if e || e6 then None
else if 100000000 <? W * H then None
else Some (YO07.mkG W H attr gen ngp gpal, 0, s6).
Definition g_opens (g : YO07.gcfg) : bool := negb ((YO07.g_w g =? 0) || (YO07.g_h g =? 0)).
Definition g_sgct (g : YO07.gcfg) : Z := if YO07.flag (YO07.g_attr g) 4 then 0 else YO07.g_ngp g.
Definition g_sgct_ok (g : YO07.gcfg) : bool := negb (256 <? g_sgct g).
Definition gs0 (g : YO07.gcfg) (loops : Z) : YO07.gif_st :=
YO07.mkS None None None 1 YO07.C_PENDING YO07.R_PENDING
[YO07.raw_header (YO07.g_w g) (YO07.g_h g) (g_sgct g) (YO07.g_gpal g) (raw_attr_of (YO07.g_attr g)) loops].
Lemma gs0_gs_new : forall g loops,
gs0 g loops = gs_new (YO07.g_w g) (YO07.g_h g) (YO07.g_attr g) (YO07.g_ngp g) loops (YO07.g_gpal g).
Proof. intros [w h a ge n p] loops. reflexivity. Qed.
Definition parse_frameN (N : Z) (s : list Z) : bool * (Z * Z * Z * Z * Z * list Z * list Z) * list Z :=
let '(e1, a, s1) := YO07.rd s 2 in let '(e2, ge, s2) := YO07.rd s1 2 in let '(e3, d, s3) := YO07.rd s2 2 in
let '(e4, t, s4) := YO07.rd s3 1 in let '(e5, n, s5) := YO07.rd s4 2 in
let attr := YO07.le_bytes a in let nlp := YO07.le_bytes n in
let '(e6, lpal, s6) := if YO07.flag attr 1 then YO07.rd s5 (nlp * 3) else (false, [], s5) in
let '(e7, img, s7) := YO07.rd s6 N in
(negb (e1 || e2 || e3 || e4 || e5 || e6 || e7), (attr, YO07.le_bytes ge, YO07.le_bytes d, YO07.le_bytes t, nlp, lpal, img), s7).
Definition parse_frame (g : YO07.gcfg) (s : list Z) := parse_frameN (YO07.g_w g * YO07.g_h g) s.
Lemma frames_loop_step : forall fuel g st s,
YO07.frames_loop (S fuel) g st s =
(let '(ok, fl, s7) := parse_frame g s in let '(attr, gen, delay, tidx, nlp, lpal, img) := fl in
if ok then YO07.frames_loop fuel g (YO07.add_frame g st attr gen delay tidx nlp lpal img) s7 else st).
Proof.
intros fuel g st s. cbn [YO07.frames_loop]. unfold parse_frame, parse_frameN.
destruct (YO07.rd s 2) as [[e1 a] s1]. destruct (YO07.rd s1 2) as [[e2 ge] s2]. destruct (YO07.rd s2 2) as [[e3 d] s3].
destruct (YO07.rd s3 1) as [[e4 t] s4]. destruct (YO07.rd s4 2) as [[e5 n] s5].
destruct (if YO07.flag (YO07.le_bytes a) 1 then YO07.rd s5 (YO07.le_bytes n * 3) else (false, [], s5)) as [[e6 lpal] s6].
destruct (YO07.rd s6 (YO07.g_w g * YO07.g_h g)) as [[e7 img] s7].
destruct (e1 || e2 || e3 || e4 || e5 || e6 || e7); reflexivity.
Qed.
Definition ff_file (g : YO07.gcfg) (loops : Z) (rest : list Z) : list Z :=
concat (YO07.close_gif g (YO07.frames_loop 16 g (gs0 g loops) rest)) ++ [59].
Definition qcount (gs : YO07.gif_st) : Z :=
(match YO07.s_q0 gs with Some _ => 1 | None => 0 end) + (match YO07.s_q1 gs with Some _ => 1 | None => 0 end) +
(match YO07.s_q2 gs with Some _ => 1 | None => 0 end).
Lemma qcount_range : forall gs, 0 <= qcount gs <= 3.
Proof. intros gs. unfold qcount. destruct (YO07.s_q0 gs), (YO07.s_q1 gs), (YO07.s_q2 gs); lia. Qed.
Lemma le_bytes_2 : forall b0 b1, YO07.le_bytes [b0; b1] = b0 + 256 * b1.
Proof. intros. unfold YO07.le_bytes. cbn [fold_right]. lia. Qed.
Lemma le_bytes_4 : forall b0 b1 b2 b3, YO07.le_bytes [b0; b1; b2; b3] = b0 + 256 * b1 + 65536 * b2 + 16777216 * b3.
Proof. intros. unfold YO07.le_bytes. cbn [fold_right]. lia. Qed.
Lemma le_bytes_1 : forall b0, YO07.le_bytes [b0] = b0.
Proof. intros. unfold YO07.le_bytes. cbn [fold_right]. lia. Qed.
Lemma rd_ok : forall s n, 0 <= n <= Z.of_nat (length s) -> YO07.rd s n = (false, firstn (Z.to_nat n) s, skipn (Z.to_nat n) s).
Proof. intros s n Hn. unfold YO07.rd. destruct (Z.ltb_spec (Z.of_nat (length s)) n); [lia | reflexivity]. Qed.
Lemma rd_short : forall s n, Z.of_nat (length s) < n -> YO07.rd s n = (true, [], []).
Proof. intros s n Hn. unfold YO07.rd. destruct (Z.ltb_spec (Z.of_nat (length s)) n); [reflexivity | lia]. Qed.
Lemma skipn_skipn_nat : forall {X} (a b : nat) (l : list X), skipn a (skipn b l) = skipn (b + a) l.
Proof. intros X a b l. rewrite skipn_skipn. f_equal. lia. Qed.
Lemma rd_at : forall P c n, 0 <= c -> 0 <= n -> c + n <= Z.of_nat (length P) ->
YO07.rd (skipn (Z.to_nat c) P) n = (false, firstn (Z.to_nat n) (skipn (Z.to_nat c) P), skipn (Z.to_nat (c + n)) P).
Proof.
intros P c n Hc Hn Hcn. rewrite rd_ok by (rewrite length_skipn; lia). f_equal. rewrite skipn_skipn_nat. f_equal. lia.
Qed.
Lemma hdr5_ok : forall P, 14 <= Z.of_nat (length P) ->
hdr5 P = (false,
(YO07.le_bytes (firstn 2 P), YO07.le_bytes (firstn 2 (skipn 2 P)), YO07.le_bytes (firstn 4 (skipn 4 P)),
YO07.le_bytes (firstn 4 (skipn 8 P)), YO07.le_bytes (firstn 2 (skipn 12 P))),
skipn 14 P).
Proof.
intros P HP. unfold hdr5.
rewrite (rd_ok P 2) by lia. change (Z.to_nat 2) with 2%nat.
rewrite (rd_ok (skipn 2 P) 2) by (rewrite length_skipn; lia). change (Z.to_nat 2) with 2%nat. rewrite (skipn_skipn_nat 2 2). cbn [Nat.add].
rewrite (rd_ok (skipn 4 P) 4) by (rewrite length_skipn; lia). change (Z.to_nat 4) with 4%nat. rewrite (skipn_skipn_nat 4 4). cbn [Nat.add].
rewrite (rd_ok (skipn 8 P) 4) by (rewrite length_skipn; lia). change (Z.to_nat 4) with 4%nat. rewrite (skipn_skipn_nat 4 8). cbn [Nat.add].
rewrite (rd_ok (skipn 12 P) 2) by (rewrite length_skipn; lia). change (Z.to_nat 2) with 2%nat. rewrite (skipn_skipn_nat 2 12). cbn [Nat.add orb].
reflexivity.
Qed.
Lemma ff_cfg_of_walk : forall P W H attr gen ngp (GPAL : list Z) cur,
hdr5 P = (false, (W, H, attr, gen, ngp), skipn 14 P) ->
W * H <= 100000000 ->
cur = 14 + (if Z.land attr 4 =? 0 then 3 * ngp else 0) -> 0 <= ngp ->
(Z.land attr 4 = 0 -> 14 + 3 * ngp <= Z.of_nat (length P) /\ GPAL = firstn (Z.to_nat (3 * ngp)) (skipn 14 P)) ->
(Z.land attr 4 <> 0 -> GPAL = []) ->
ff_cfg P = Some (YO07.mkG W H attr gen ngp GPAL, 0, skipn (Z.to_nat cur) P).
Proof.
intros P W H attr gen ngp GPAL cur Hh HWH Hcur Hngp Hg Hng. unfold ff_cfg. rewrite Hh. unfold YO07.flag. subst cur.
destruct (Z.eqb_spec (Z.land attr 4) 0) as [E|E]; cbn [negb].
- destruct (Hg E) as [Hlen ->]. change (skipn 14 P) with (skipn (Z.to_nat 14) P). rewrite (rd_at P 14 (ngp * 3)) by lia. cbn [orb].
destruct (Z.ltb_spec 100000000 (W * H)); [lia|]. replace (ngp * 3) with (3 * ngp) by lia. reflexivity.
- cbn [orb]. destruct (Z.ltb_spec 100000000 (W * H)); [lia|]. rewrite (Hng E). replace (14 + 0) with 14 by lia. reflexivity.
Qed.
