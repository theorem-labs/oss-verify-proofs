(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YK0k.v, with its module paths changed. *)
(* Modified by Rares Buhai, 2026-10: changed module paths to the MayFail runtime. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK16.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0n.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK11.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0i.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0h.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK14.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK1c.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK1i.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK1d.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK0v.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK15.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable.R Require Import Cfg.
Unset Lia Cache. Unset Nia Cache.
Import ListNotations.
Open Scope bv_scope.
Definition rd_adm (s : InputStream) (cnt : word) (bs : list byte) : Prop :=
(bs = [] /\ s = IEof)
\/ ((1 <= Z.of_nat (length bs))%Z
/\ (Z.of_nat (length bs) <= bv_unsigned cnt)%Z
/\ fst (stream_take s (length bs)) = bs).
Definition RdIdx (s : InputStream) (cnt : word) : Type :=
{ bs : list byte | rd_adm s cnt bs }.
Lemma rd_adm_inhab : forall s cnt, (0 < bv_unsigned cnt)%Z ->
exists bs, rd_adm s cnt bs.
Proof.
intros [|b s'] cnt Hcnt.
- exists []. left. split; reflexivity.
- exists [b]. right. cbn [length].
split; [lia | split; [lia | reflexivity]].
Qed.
Lemma rd_adm_eof_nil : forall s cnt bs, rd_adm s cnt bs -> bs = [] -> s = IEof.
Proof.
intros s cnt bs [(_ & Hs) | (Hlo & _ & _)] ->; [exact Hs | cbn in Hlo; lia].
Qed.
Lemma rd_adm_block_nonnil : forall bs : list byte,
(1 <= Z.of_nat (length bs))%Z -> bs <> [].
Proof. intros [|b bs] H; [cbn in H; lia | discriminate]. Qed.
Definition rd_next (ms : machine_state) (model : Model) (buf : word)
(bs : list byte) : config :=
match bs with
| [] => mkCfg (advance_past_svc (set_gpr0 ms (Z_to_bv 64 0))) model
| _ :: _ =>
mkCfg (advance_past_svc (apply_effect ms (mkEffect (len_word bs) [(buf, bs)] [])))
(with_stdin (snd (stream_take (m_stdin model) (length bs))) model)
end.
Lemma rd_next_stdin_block : forall ms model buf bs, bs <> [] ->
m_stdin (cfg_model (rd_next ms model buf bs))
= snd (stream_take (m_stdin model) (length bs)).
Proof. intros ms model buf [|b bs] H; [congruence | reflexivity]. Qed.
Definition stream_firstn (s : InputStream) (k : nat) : list byte :=
fst (stream_take s k).
Lemma stream_take_split : forall k1 k2 s,
fst (stream_take s (k1 + k2))
= fst (stream_take s k1)
++ fst (stream_take (snd (stream_take s k1)) k2).
Proof.
induction k1 as [|k1 IH]; intros k2 s; [reflexivity|].
destruct s as [|b s']; cbn [stream_take fst snd Nat.add].
- rewrite (stream_take_nil_of_eof k2). reflexivity.
- rewrite IH. reflexivity.
Qed.
Lemma stream_take_cons_pos : forall b s k, (1 <= k)%nat ->
fst (stream_take (ICons b s) k) = b :: fst (stream_take s (k - 1)).
Proof.
intros b s [|k] H; [lia|].
cbn [stream_take fst]. replace (S k - 1)%nat with k by lia. reflexivity.
Qed.
Lemma stream_take_ge : forall k1 k2 s,
(k1 <= k2)%nat ->
(length (fst (stream_take s k1)) < k1)%nat ->
fst (stream_take s k2) = fst (stream_take s k1).
Proof.
induction k1 as [|k1 IH]; intros k2 s Hle Hlen; [cbn in Hlen; lia|].
destruct k2 as [|k2]; [lia|].
destruct s as [|b s']; cbn [stream_take fst snd] in *; [reflexivity|].
cbn [length] in Hlen. rewrite (IH k2 s'); [reflexivity | lia | lia].
Qed.
Lemma stream_take_app_take : forall s bs k,
fst (stream_take s (length bs)) = bs ->
bs ++ fst (stream_take (snd (stream_take s (length bs))) k)
= fst (stream_take s (length bs + k)).
Proof.
intros s bs k Hpre. rewrite stream_take_split, Hpre. reflexivity.
Qed.
Section d.
Variable segs : list Segment.
Lemma node_read0 : forall ms model buf cnt x8 w,
(0 < bv_unsigned cnt <= rw_bytes_max)%Z ->
m_halted model = None ->
m_vm_lazy model = [] ->
fd_lookup (m_fds model) (Z_to_bv 64 0) = Some (FdChannel (Z_to_bv 64 0)) ->
ms_svc_pending ms = Some x8 ->
bv_unsigned x8 = 63%Z ->
ms_gpr ms 0 = Z_to_bv 64 0 ->
ms_gpr ms 1 = buf ->
ms_gpr ms 2 = cnt ->
read_bytes_map (ms_writable_byte segs ms) buf cnt = Some w ->
access_okb buf (bv_unsigned cnt) = true ->
node_ok segs (mkCfg ms model) (RdIdx (m_stdin model) cnt)
(fun i => map (ReadEv (Z_to_bv 64 0)) (proj1_sig i))
(fun i => rd_next ms model buf (proj1_sig i)).
Proof.
intros ms model buf cnt x8 w Hcnt Hh Hlazy Hfd Hsvc Hno Hg0 Hg1 Hg2 Hw Haok.
apply node_ok_of_pnode; [eapply transparent_nonalloc_no; [exact Hsvc | exact Hno | reflexivity]|]. split.
-
intros [bs Hadm]; cbn [proj1_sig].
destruct Hadm as [(-> & Heof) | (Hlo & Hhi & Hpre)].
+
cbn [map rd_next].
rewrite <- (apply_effect_no_write ms (Z_to_bv 64 0)).
apply (sstep_syscall segs ms model x8 (mkEffect (Z_to_bv 64 0) [] []) model model []);
[exact Hh | exact Hsvc
| eapply (read0_ok_eof cnt Hcnt segs ms x8 model w); try eassumption;
rewrite Hg1; assumption
| exact Hh |].
rewrite (materialize_model_accesses_no_lazy model _ Hlazy). reflexivity.
+
assert (Hne : bs <> []) by (destruct bs; [cbn in Hlo; lia | discriminate]).
destruct bs as [|b0 bs0]; [congruence|].
cbn [rd_next].
apply (sstep_syscall segs ms model x8
(mkEffect (len_word (b0 :: bs0)) [(buf, b0 :: bs0)] [])
(with_stdin (snd (stream_take (m_stdin model) (length (b0 :: bs0)))) model)
(with_stdin (snd (stream_take (m_stdin model) (length (b0 :: bs0)))) model)
(map (ReadEv (Z_to_bv 64 0)) (b0 :: bs0)));
[exact Hh | exact Hsvc | | rewrite m_halted_with_stdin; exact Hh |].
* rewrite <- Hg1.
eapply (read0_ok_bytes cnt Hcnt segs ms x8 model w); try eassumption;
rewrite Hg1; assumption.
* rewrite (materialize_model_accesses_no_lazy _ _).
-- reflexivity.
-- rewrite m_vm_lazy_with_stdin. exact Hlazy.
-
intros e st Hss.
destruct (sstep_read_inv cnt Hcnt segs ms model buf x8 w e st
Hh Hlazy Hfd Hsvc Hno Hg0 Hg1 Hg2 Hw Haok Hss)
as [(Heof & -> & ->) | (bs & Hlo & Hhi & Hpre & -> & ->)].
+ exists (exist _ [] (or_introl (conj eq_refl Heof))). split; reflexivity.
+ assert (Hadm : rd_adm (m_stdin model) cnt bs)
by (right; split; [exact Hlo | split; [exact Hhi | exact Hpre]]).
exists (exist _ bs Hadm). cbn [proj1_sig].
destruct bs as [|b0 bs0]; [cbn in Hlo; lia|].
split; reflexivity.
Qed.
Definition t_read_ch (rch : word) (s : InputStream) (cnt : word)
(K : list byte -> TSet) : TSet :=
t_alt (fun i : RdIdx s cnt =>
t_emit (map (ReadEv rch) (proj1_sig i)) (K (proj1_sig i))).
Definition t_read0 (s : InputStream) (cnt : word) (K : list byte -> TSet) : TSet :=
t_read_ch (Z_to_bv 64 0) s cnt K.
Lemma rz_read0 : forall ms model buf cnt x8 w K,
(0 < bv_unsigned cnt <= rw_bytes_max)%Z ->
m_halted model = None ->
m_vm_lazy model = [] ->
fd_lookup (m_fds model) (Z_to_bv 64 0) = Some (FdChannel (Z_to_bv 64 0)) ->
ms_svc_pending ms = Some x8 ->
bv_unsigned x8 = 63%Z ->
ms_gpr ms 0 = Z_to_bv 64 0 ->
ms_gpr ms 1 = buf ->
ms_gpr ms 2 = cnt ->
read_bytes_map (ms_writable_byte segs ms) buf cnt = Some w ->
access_okb buf (bv_unsigned cnt) = true ->
(forall bs, rd_adm (m_stdin model) cnt bs ->
realizes segs (rd_next ms model buf bs) (K bs)) ->
realizes segs (mkCfg ms model) (t_read0 (m_stdin model) cnt K).
Proof.
intros ms model buf cnt x8 w K Hcnt Hh Hlazy Hfd Hsvc Hno Hg0 Hg1 Hg2 Hw Haok HK.
destruct (rd_adm_inhab (m_stdin model) cnt (proj1 Hcnt)) as [bs0 Hbs0].
unfold t_read0, t_read_ch.
apply (rz_node segs (mkCfg ms model) (RdIdx (m_stdin model) cnt)
(fun i => map (ReadEv (Z_to_bv 64 0)) (proj1_sig i))
(fun i => rd_next ms model buf (proj1_sig i))
(fun i => K (proj1_sig i))
(exist _ bs0 Hbs0)).
- eapply node_read0; eassumption.
- intros [bs Hbs]; cbn [proj1_sig]. apply HK; exact Hbs.
Qed.
Lemma t_emit_app : forall a b T, t_eq (t_emit a (t_emit b T)) (t_emit (a ++ b) T).
Proof.
intros a b T tr. unfold t_emit. split.
- intros [Hp | (tr' & -> & [Hp | (tr'' & -> & HT)])].
+ left. apply is_prefix_app_r. exact Hp.
+ left. apply is_prefix_app_mono. exact Hp.
+ right. exists tr''. rewrite app_assoc. split; [reflexivity | exact HT].
- intros [Hp | (tr' & -> & HT)].
+ apply is_prefix_app_split in Hp as [Hp | (tr' & -> & Hp)].
* left. exact Hp.
* right. exists tr'. split; [reflexivity | left; exact Hp].
+ right. exists (b ++ tr').
split; [symmetry; apply app_assoc
| right; exists tr'; split; [reflexivity | exact HT]].
Qed.
Lemma t_emit_cong : forall e T T', t_eq T T' -> t_eq (t_emit e T) (t_emit e T').
Proof.
intros e T T' H tr. unfold t_emit. split;
intros [Hp | (tr' & -> & HT)];
solve [ left; exact Hp
| right; exists tr'; split; [reflexivity | apply H; exact HT] ].
Qed.
Section f.
Variable cap : nat.
Hypothesis Hcap : (Z.of_nat cap < 2 ^ 64)%Z.
Hypothesis Hcap_modeled : (Z.of_nat cap <= rw_bytes_max)%Z.
Variable LH : list byte -> config -> Prop.
Variable Tfin : list byte -> TSet.
Definition dcnt (acc : list byte) : word := Z_to_bv 64 (Z.of_nat (cap - length acc)).
Lemma dcnt_pos : forall acc, (length acc < cap)%nat -> (0 < bv_unsigned (dcnt acc))%Z.
Proof.
intros acc H. unfold dcnt. rewrite Z_to_bv_unsigned.
unfold bv_wrap, bv_modulus. cbn [Z.of_N].
rewrite Z.mod_small; lia.
Qed.
Lemma dcnt_max : forall acc, (length acc <= cap)%nat ->
(bv_unsigned (dcnt acc) <= rw_bytes_max)%Z.
Proof.
intros acc H. unfold dcnt. rewrite Z_to_bv_unsigned.
unfold bv_wrap, bv_modulus. cbn [Z.of_N].
rewrite Z.mod_small; lia.
Qed.
Lemma dcnt_val : forall acc, (length acc <= cap)%nat ->
bv_unsigned (dcnt acc) = Z.of_nat (cap - length acc).
Proof.
intros acc H. unfold dcnt. rewrite Z_to_bv_unsigned.
unfold bv_wrap, bv_modulus. cbn [Z.of_N]. rewrite Z.mod_small; lia.
Qed.
Fixpoint t_drain_ch (rch : word) (n : nat) (s : InputStream) (acc : list byte)
: TSet :=
match n with
| O => Tfin acc
| S n' =>
if (cap <=? length acc)%nat then Tfin acc
else t_read_ch rch s (dcnt acc)
(fun bs =>
match bs with
| [] => Tfin acc
| _ :: _ =>
t_drain_ch rch n' (snd (stream_take s (length bs))) (acc ++ bs)
end)
end.
Definition t_drain (n : nat) (s : InputStream) (acc : list byte) : TSet :=
t_drain_ch (Z_to_bv 64 0) n s acc.
Hypothesis Htfin_ne : forall acc, Tfin acc [].
Lemma t_drain_ch_collapse : forall rch n s acc,
(cap - length acc <= n)%nat ->
(length acc <= cap)%nat ->
t_eq (t_drain_ch rch n s acc)
(t_emit (map (ReadEv rch) (fst (stream_take s (cap - length acc))))
(Tfin (acc ++ fst (stream_take s (cap - length acc))))).
Proof.
intro rch. induction n as [|n IH]; intros s acc Hn Hle.
-
replace (cap - length acc)%nat with O by lia.
cbn [stream_take fst map]. rewrite app_nil_r.
apply t_eq_sym, t_emit_nil_eq, Htfin_ne.
- cbn [t_drain_ch].
destruct (Nat.leb_spec cap (length acc)) as [Hfullc | Hlt].
+ replace (cap - length acc)%nat with O by lia.
cbn [stream_take fst map]. rewrite app_nil_r.
apply t_eq_sym, t_emit_nil_eq, Htfin_ne.
+
set (m := (cap - length acc)%nat).
assert (Hm : (1 <= m)%nat) by (unfold m; lia).
assert (Hdc : bv_unsigned (dcnt acc) = Z.of_nat m)
by (apply dcnt_val; lia).
intro tr. unfold t_read_ch, t_alt. split.
*
intros [[bs Hadm] Hi]; cbn [proj1_sig] in Hi.
destruct bs as [|b0 bs0].
{
destruct Hadm as [(_ & ->) | (Hlo & _ & _)]; [|cbn in Hlo; lia].
rewrite stream_take_nil_of_eof, app_nil_r. exact Hi. }
{
set (bs := b0 :: bs0) in *.
destruct Hadm as [(Hbad & _) | (Hlo & Hhi & Hpre)]; [discriminate|].
assert (Hblen : (length bs <= m)%nat) by (rewrite Hdc in Hhi; lia).
assert (Hlen' : length (acc ++ bs) = (length acc + length bs)%nat)
by (rewrite length_app; reflexivity).
assert (Hsplit :
fst (stream_take s m)
= bs ++ fst (stream_take (snd (stream_take s (length bs)))
(m - length bs)))
by (replace m with (length bs + (m - length bs))%nat at 1 by lia;
rewrite stream_take_split, Hpre; reflexivity).
pose proof (IH (snd (stream_take s (length bs))) (acc ++ bs)
ltac:(lia) ltac:(lia)) as IHb.
replace (cap - length (acc ++ bs))%nat with (m - length bs)%nat
in IHb by lia.
rewrite <- app_assoc in IHb.
rewrite Hsplit, map_app.
apply (proj1 (t_emit_app (map (ReadEv rch) bs) _ _ tr)).
exact (proj1 (t_emit_cong _ _ _ IHb tr) Hi). }
*
intro Hrhs.
destruct s as [|b s'].
{
unshelve eexists (exist _ [] _); [left; split; reflexivity|].
cbn [proj1_sig]. rewrite stream_take_nil_of_eof, app_nil_r in Hrhs.
exact Hrhs. }
{
unshelve eexists (exist _ [b] _).
{ right. cbn [length]. split; [lia | split; [lia | reflexivity]]. }
cbn [proj1_sig length stream_take fst snd map].
assert (Hlen' : length (acc ++ [b]) = S (length acc))
by (rewrite length_app; cbn [length]; lia).
pose proof (IH s' (acc ++ [b]) ltac:(lia) ltac:(lia)) as IHb.
replace (cap - length (acc ++ [b]))%nat with (m - 1)%nat in IHb by lia.
rewrite <- app_assoc in IHb. cbn [app] in IHb.
apply (proj2 (t_emit_cong [ReadEv rch b] _ _ IHb tr)).
apply (proj2 (t_emit_app [ReadEv rch b]
(map (ReadEv rch)
(fst (stream_take s' (m - 1)))) _ tr)).
rewrite (stream_take_cons_pos b s' m Hm) in Hrhs.
cbn [map app] in Hrhs |- *. exact Hrhs. }
Qed.
Lemma t_drain_collapse : forall n s acc,
(cap - length acc <= n)%nat ->
(length acc <= cap)%nat ->
t_eq (t_drain n s acc)
(t_emit (map (ReadEv (Z_to_bv 64 0)) (fst (stream_take s (cap - length acc))))
(Tfin (acc ++ fst (stream_take s (cap - length acc))))).
Proof. exact (t_drain_ch_collapse (Z_to_bv 64 0)). Qed.
Corollary t_drain_ch_top_collapse : forall rch s,
t_eq (t_drain_ch rch cap s [])
(t_emit (map (ReadEv rch) (stream_firstn s cap))
(Tfin (stream_firstn s cap))).
Proof.
intros rch s. unfold stream_firstn.
pose proof (t_drain_ch_collapse rch cap s [] ltac:(cbn [length]; lia)
ltac:(cbn [length]; lia)) as H.
replace (cap - length (@nil byte))%nat with cap in H
by (cbn [length]; lia).
cbn [app] in H. exact H.
Qed.
Corollary t_drain_top_collapse : forall s,
t_eq (t_drain cap s [])
(t_emit (map (ReadEv (Z_to_bv 64 0)) (stream_firstn s cap))
(Tfin (stream_firstn s cap))).
Proof. exact (t_drain_ch_top_collapse (Z_to_bv 64 0)). Qed.
Hypothesis Hfull : forall acc c,
LH acc c -> (cap <= length acc)%nat -> realizes segs c (Tfin acc).
Hypothesis Hread : forall acc c,
LH acc c -> (length acc < cap)%nat ->
exists ms1 buf x8 w,
m_halted (cfg_model c) = None /\
m_vm_lazy (cfg_model c) = [] /\
fd_lookup (m_fds (cfg_model c)) (Z_to_bv 64 0) = Some (FdChannel (Z_to_bv 64 0)) /\
msteps segs (cfg_ms c) ms1 /\
ms_svc_pending ms1 = Some x8 /\
bv_unsigned x8 = 63%Z /\
ms_gpr ms1 0 = Z_to_bv 64 0 /\
ms_gpr ms1 1 = buf /\
ms_gpr ms1 2 = dcnt acc /\
read_bytes_map (ms_writable_byte segs ms1) buf (dcnt acc) = Some w /\
access_okb buf (bv_unsigned (dcnt acc)) = true /\
realizes segs (rd_next ms1 (cfg_model c) buf []) (Tfin acc) /\
(forall bs, rd_adm (m_stdin (cfg_model c)) (dcnt acc) bs -> bs <> [] ->
LH (acc ++ bs) (rd_next ms1 (cfg_model c) buf bs)).
Lemma rz_drain : forall n acc c,
(cap - length acc <= n)%nat ->
LH acc c ->
realizes segs c (t_drain n (m_stdin (cfg_model c)) acc).
Proof.
induction n as [|n IH]; intros acc c Hn HLH.
- cbn [t_drain t_drain_ch]. apply Hfull; [exact HLH | lia].
- cbn [t_drain t_drain_ch].
destruct (Nat.leb_spec cap (length acc)) as [Hle | Hlt].
+ apply Hfull; [exact HLH | exact Hle].
+ destruct (Hread acc c HLH Hlt)
as (ms1 & buf & x8 & w & Hh & Hlazy & Hfd & Hms & Hsvc & Hno & Hg0 & Hg1 & Hg2 & Hw
& Haok & Heof & Hblk).
destruct c as [ms0 model]; cbn [cfg_ms cfg_model] in *.
eapply rz_msteps; [exact Hh | exact Hlazy | exact Hms |].
apply (rz_read0 ms1 model buf (dcnt acc) x8 w);
try assumption;
[split; [apply dcnt_pos; exact Hlt | apply dcnt_max; lia] |].
intros bs Hadm. destruct bs as [|b0 bs0].
* exact Heof.
* specialize (Hblk (b0 :: bs0) Hadm ltac:(discriminate)).
specialize (IH (acc ++ b0 :: bs0) _ ltac:(
rewrite length_app; cbn [length]; lia) Hblk).
rewrite (rd_next_stdin_block ms1 model buf (b0 :: bs0) ltac:(discriminate))
in IH.
exact IH.
Qed.
Corollary rz_drain_top : forall c,
LH [] c -> realizes segs c (t_drain cap (m_stdin (cfg_model c)) []).
Proof. intros c H. apply rz_drain; [cbn [length]; lia | exact H]. Qed.
Lemma t_alt2_cong : forall A A' B B',
t_eq A A' -> t_eq B B' -> t_eq (t_alt2 A B) (t_alt2 A' B').
Proof.
intros A A' B B' HA HB tr. unfold t_alt2.
split; (intros [H | H]; [left; apply HA; exact H | right; apply HB; exact H]).
Qed.
End f.
End d.
