(** * Bridge.IProbe — INTERFACE (part C lead): non-vacuity of the state relations.

    A relation no real state satisfies would make every pair lemma vacuous.
    These probes compute both models' states at the harness's entry points
    and check the relations with the boolean checkers (whose soundness is
    proved in [IRelDefl] / [IRelInfl]):

    - deflate: S5's state just after [deflate_m] installs the call's stream
      (init by [HarnessCompress.dsC level], then [set_strm]) against RT's
      [defl_new level 8 15 8 0] with the same call installed, for every
      level 0..9 — [dst_rel] holds, with [pre_out = pre_in = []];
    - inflate: S5's [ZApiInst.is0] against RT's [inflateInit2 z_fresh
      state_fresh 15] — [is_rel] holds.

    Each probe also shows the checker REJECTS a perturbed state (planted
    positive), so a true answer is evidence and not a checker that always
    says yes. *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require ZIface DeflateState HarnessCompress ZApiInst.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Deflate Inflate Codec.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge Require Import IRelArr IRelDefl IRelInfl.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Definition probe_data : list Z := [72; 101; 108; 108; 111; 44; 32; 122; 108; 105; 98; 33].

Definition s5_entry (level : Z) (data : list Z) : DS.deflate_state :=
  let cb := OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z.Deflate.compressBound_m (ZIface.zlength data) in
  DS.set_strm (HarnessCompress.dsC level)
              (DS.cstrm_of_call (ZIface.mkZCall data cb (HarnessCompress.dzC level))).

Definition rt_entry (level : Z) (data : list Z) : option RD.DSt :=
  let cb := OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z.Deflate.compressBound_m (ZIface.zlength data) in
  match RD.defl_new level 8 15 8 0 with
  | None => None
  | Some t0 => Some (RD.setD_strm (RD.setZ_availout cb (RD.setZ_in data (RD.d_strm t0))) t0)
  end.

Definition entry_ok (level : Z) : bool :=
  match rt_entry level probe_data with
  | Some t => dst_relb (s5_entry level probe_data) t [] []
  | None => false
  end.

(** Per-cluster answers, so a failure names its cluster. *)
Definition entry_clusters (level : Z) : list bool :=
  match rt_entry level probe_data with
  | Some t => let s := s5_entry level probe_data in
      [geom_relb s t; lz_relb s t; bw_relb s (RT.ts_bw (RD.d_ts t)); sym_relb s t;
       tree_relb s t; strm_relb s t [] []]
  | None => []
  end.

Example probe_deflate_entry_all_levels :
  map entry_ok [0; 1; 2; 3; 4; 5; 6; 7; 8; 9] = repeat true 10.
Proof. vm_compute. reflexivity. Qed.

Theorem deflate_entry_related : forall level, In level [0; 1; 2; 3; 4; 5; 6; 7; 8; 9] ->
  exists t, rt_entry level probe_data = Some t /\ dst_rel (s5_entry level probe_data) t [] [].
Proof.
  intros level Hin.
  assert (Hok : entry_ok level = true)
    by (repeat destruct Hin as [<-|Hin]; [vm_compute; reflexivity ..| destruct Hin]).
  unfold entry_ok in Hok. destruct (rt_entry level probe_data) as [t|] eqn:E; [|discriminate].
  exists t. split; [reflexivity|]. apply dst_relb_sound, Hok.
Qed.

(** Planted positive: a one-byte change to S5's window makes the checker say no. *)
Example probe_deflate_checker_rejects :
  match rt_entry 6 probe_data with
  | Some t => dst_relb (DS.set_window (s5_entry 6 probe_data)
                          (ZIface.arr_set (DS.ds_window (s5_entry 6 probe_data)) 100 7)) t [] []
  | None => true
  end = false.
Proof. vm_compute. reflexivity. Qed.

(* ------------------------------------------------------------------------- *)

Definition rt_istate0 : option RI.IState :=
  match RI.inflateInit2 Codec.z_fresh Codec.state_fresh 15 with
  | Some (_, st) => Some st
  | None => None
  end.

Example probe_inflate_init :
  match rt_istate0 with Some st => is_relb ZApiInst.is0 st | None => false end = true.
Proof. vm_compute. reflexivity. Qed.

Theorem inflate_init_related : exists st, rt_istate0 = Some st /\ is_rel ZApiInst.is0 st.
Proof.
  destruct rt_istate0 as [st|] eqn:E.
  - exists st. split; [reflexivity|]. apply is_relb_sound.
    pose proof probe_inflate_init as H. rewrite E in H. exact H.
  - pose proof probe_inflate_init as H. rewrite E in H. discriminate.
Qed.

Example probe_inflate_checker_rejects :
  match rt_istate0 with
  | Some st => is_relb (IS.iset_mode ZApiInst.is0 (IS.is_mode ZApiInst.is0 + 1)) st
  | None => true
  end = false.
Proof. vm_compute. reflexivity. Qed.

Print Assumptions deflate_entry_related.
Print Assumptions inflate_init_related.
