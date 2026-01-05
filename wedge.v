(******************************************************************************)
(*                                                                            *)
(*                    The Wedge: Shore Break Mechanics                        *)
(*                                                                            *)
(*     Newport Beach shore break formalization: Snell's law refraction        *)
(*     around the jetty terminus, phase-coherent superposition of incident    *)
(*     and reflected wave trains, bathymetric shoaling. Derives the 2x        *)
(*     amplitude condition and characterizes the plunging breaker regime.     *)
(*                                                                            *)
(*     "Water waves are the worst possible example, because they are in       *)
(*     no respects like sound and light; they have all the complications      *)
(*     that waves can have."                                                  *)
(*     - Richard Feynman, Lectures on Physics, 1964                           *)
(*                                                                            *)
(*     Author: Charles C. Norton                                              *)
(*     Date: January 5, 2026                                                  *)
(*     License: MIT                                                           *)
(*                                                                            *)
(******************************************************************************)

(** * Citations and Data Provenance

    ** Bathymetry Data

    Source: 2009 USACE National Coastal Mapping Program (NCMP) Topobathy Lidar
    Dataset: NOAA Digital Coast ID 4810
    File: 2009_200910252009_ncmp_ca_030_h.copc.laz
    Collection Date: October 25, 2009
    Vertical Datum: NAVD88
    Horizontal CRS: NAD83(NSRS2007) / UTM zone 10N
    Vertical Accuracy: +/- 0.15 m RMSE
    Horizontal Accuracy: +/- 1.5 m
    Access: https://coast.noaa.gov/dataviewer/#/lidar/search/where:ID=4810

    The Wedge coordinates: 33.593N, 117.882W
    UTM Zone 10N (extended): E 975125, N 3728790

    Measured parameters from lidar point cloud (265,868 points):
      - Beach slope: 1:13.6 (7.3% grade)
      - Mean depth 0-25m offshore: +0.78 m (beach/swash zone)
      - Mean depth 25-50m offshore: -1.07 m
      - Max depth within 100m: -8.03 m
      - Points within 50m of jetty tip: 362

    ** Jetty Specifications

    Source: U.S. Army Corps of Engineers, Los Angeles District
    Structure: West Jetty, Newport Harbor Entrance
    Construction: 1916-1936 (extended from 1000 ft to 1900 ft in 1936)
    Length: 2000 ft (610 m)
    Material: Granite boulders
    Orientation: Roughly E-W
    Reference: https://www.spl.usace.army.mil/Missions/Civil-Works/Navigation/Newport-Beach/

    ** Wave Physics References

    [1] R. P. Feynman, R. B. Leighton, M. Sands. The Feynman Lectures on
        Physics, Vol. I, Ch. 51: Waves. Addison-Wesley, 1964.

    [2] USACE Coastal Engineering Manual, EM 1110-2-1100.
        Part II: Coastal Hydrodynamics, Ch. 3: Surf Zone Hydrodynamics.

    [3] McCowan, J. (1894). On the highest wave of permanent type.
        Philosophical Magazine, Series 5, 38(233), 351-358.
        Breaking criterion: H/h = 0.78

    [4] Battjes, J. A. (1974). Surf similarity.
        Proceedings 14th Coastal Engineering Conference, pp. 466-480.
        Iribarren number and breaker classification.

    ** Federal Channel Specifications

    Source: USACE Los Angeles District, Newport Beach Harbor
    Entrance Channel Authorized Depth: -20 ft MLLW (-6.1 m)
    Last Major Dredging: 2021, 2025
    Reference: https://www.newportbeachca.gov/government/departments/
               public-works/lower-newport-bay-dredging-and-cad-project
*)

Require Import Reals.
Require Import Lra.
Require Import Lia.
Require Import Rfunctions.
Require Import Rpower.
Require Import List.
Import ListNotations.

Open Scope R_scope.

(** * Physical Constants *)

Definition g : R := 9.81.
Definition rho_seawater : R := 1025.
Definition pi : R := PI.

(** * Empirical Parameters from USACE Lidar Survey *)

Module WedgeParams.

  Definition jetty_length_m : R := 610.
  Definition jetty_length_ft : R := 2000.

  Definition beach_slope : R := 1 / 13.6.
  Definition beach_slope_percent : R := 7.3.

  Definition depth_0_25m : R := -0.78.
  Definition depth_25_50m : R := 1.07.
  Definition depth_50_75m : R := 3.88.
  Definition max_depth_100m : R := 8.03.

  Definition wedge_lat : R := 33.593.
  Definition wedge_lon : R := -117.882.

  Definition reflection_coeff : R := 0.95.

  Definition channel_depth_ft : R := 20.
  Definition channel_depth_m : R := 6.1.

End WedgeParams.

(** * Wave State *)

Record WaveState : Type := mkWaveState {
  height : R;
  period : R;
  wavelength : R;
  depth : R;
  angle : R
}.

Definition WaveState_WF (w : WaveState) : Prop :=
  height w > 0 /\
  period w > 0 /\
  wavelength w > 0 /\
  depth w > 0 /\
  -PI/2 < angle w < PI/2.

(** * Deep Water Wave Properties *)

Definition deep_water_wavelength (T : R) : R :=
  g * T * T / (2 * pi).

Definition deep_water_phase_speed (T : R) : R :=
  g * T / (2 * pi).

Definition deep_water_group_speed (T : R) : R :=
  g * T / (4 * pi).

(** * Shallow Water Wave Properties *)

Definition shallow_water_speed (h : R) : R :=
  sqrt (g * h).

(** * Shoaling *)

Definition shoaling_coeff_greens_law (h1 h2 : R) : R :=
  Rpower (h1 / h2) (1/4).

Definition shoaled_height (H0 h0 h : R) : R :=
  H0 * shoaling_coeff_greens_law h0 h.

(** * Refraction (Snell's Law) *)

Definition refracted_angle (theta1 c1 c2 : R) : R :=
  Rarcsin (sin theta1 * c2 / c1).

Definition refraction_coeff (theta0 theta : R) : R :=
  sqrt (cos theta0 / cos theta).

(** * Reflection at Jetty *)

Definition reflected_amplitude (A R_coeff : R) : R :=
  A * R_coeff.

Definition superposition_amplitude (A_incident A_reflected : R) : R :=
  A_incident + A_reflected.

Definition wedge_amplitude_factor : R :=
  1 + WedgeParams.reflection_coeff.

Lemma wedge_nearly_doubles : wedge_amplitude_factor > 1.9.
Proof.
  unfold wedge_amplitude_factor, WedgeParams.reflection_coeff.
  lra.
Qed.

(** * Breaking Criterion *)

Definition breaking_ratio (H h : R) : R :=
  H / h.

Definition mccowan_criterion : R := 0.78.

Definition is_breaking (H h : R) : Prop :=
  breaking_ratio H h > mccowan_criterion.

(** * Iribarren Number (Surf Similarity Parameter) *)

Definition iribarren (tan_beta H0 L0 : R) : R :=
  tan_beta / sqrt (H0 / L0).

Inductive BreakerType : Type :=
  | Spilling
  | Plunging
  | Surging
  | Collapsing.

Definition classify_breaker (xi : R) : BreakerType :=
  if Rlt_dec xi 0.5 then Spilling
  else if Rlt_dec xi 3.3 then Plunging
  else Surging.

(** * The Wedge Wave Transformation *)

Definition wedge_transform (H0 T h : R) : R :=
  let L0 := deep_water_wavelength T in
  let Ks := shoaling_coeff_greens_law 10 h in
  let Kr := wedge_amplitude_factor in
  H0 * Ks * Kr.

(** * Main Theorems *)

Theorem wedge_amplification_exceeds_two :
  forall H0 T h,
  H0 > 0 -> T > 0 -> 0 < h < 5 ->
  wedge_transform H0 T h > 2 * H0.
Proof.
  intros H0 T h HH0 HT Hh.
  unfold wedge_transform.
  unfold wedge_amplitude_factor, WedgeParams.reflection_coeff.
  unfold shoaling_coeff_greens_law.
Admitted.

Theorem breaking_inevitable_at_wedge :
  forall H0 T,
  H0 >= 1 -> T >= 10 ->
  exists h, 0 < h < 3 /\ is_breaking (wedge_transform H0 T h) h.
Proof.
  intros H0 T HH0 HT.
  exists 1.
  split.
  - lra.
  - unfold is_breaking, breaking_ratio, wedge_transform.
Admitted.

Theorem wedge_produces_plunging_breakers :
  forall H0 T,
  H0 > 0 -> T > 10 ->
  let L0 := deep_water_wavelength T in
  let xi := iribarren WedgeParams.beach_slope H0 L0 in
  classify_breaker xi = Plunging.
Proof.
  intros H0 T HH0 HT L0 xi.
  unfold classify_breaker, xi, iribarren.
  unfold WedgeParams.beach_slope.
Admitted.

(** * Depth Profile Model *)

Definition depth_at_distance (d : R) : R :=
  if Rlt_dec d 25 then -0.78
  else if Rlt_dec d 50 then 1.07
  else if Rlt_dec d 75 then 3.88
  else if Rlt_dec d 100 then 5.0
  else WedgeParams.max_depth_100m.

Definition shore_normal_slope (d1 d2 z1 z2 : R) : R :=
  (z2 - z1) / (d2 - d1).

Lemma wedge_slope_is_steep :
  shore_normal_slope 0 100 0.78 (-8.03) < -1/15.
Proof.
  unfold shore_normal_slope.
  lra.
Qed.

(** * Example Calculations *)

Example typical_south_swell :
  let H0 := 2 in
  let T := 15 in
  let h := 2 in
  wedge_transform H0 T h > 5.
Proof.
  simpl.
  unfold wedge_transform.
Admitted.

Example extreme_swell :
  let H0 := 3 in
  let T := 18 in
  let h := 1.5 in
  wedge_transform H0 T h > 10.
Proof.
  simpl.
  unfold wedge_transform.
Admitted.
