# MD3B
An application for determining blood-brain barrier permeability from umbrella sampling simulations.
<img width="2878" height="2631" alt="logo_bilayer" src="https://github.com/user-attachments/assets/66158215-bc85-447d-a2ac-875183fbe6f6" />
The MD3B application is developed for processing MD simulations based on the Inhomogeneous Solubility-Diffusion Model and the formalism published in the article 'A method to predict blood-brain barrier permeability of drug-like compounds using molecular dynamics simulations' [Biophysical Journal 107 (2014): 630–641]. It can predict the brain to blood (LogBB) partition of drug-like molecules.

In summary, the key structural and algorithmic achievements in the software architecture include:

•	The exact replication of the log-linear autocovariance methodology by Hummer for extracting the relaxation time τz and calculating the localized diffusion coefficient D(z), coupled with the proper handling of the requisite noise floor truncation.

•	The implementation of an advanced statistical scoring algorithm to dynamically optimize block-averaging intervals, thereby neutralizing the primary source of user error in diffusivity profiling and adapting seamlessly to the heterogeneous viscosity gradients inherent in lipid bilayers.

•	The highly accurate rendering of the parallel pathway permeation model, appropriately combining charged and neutral potential of mean force profiles offset by the precise Henderson-Hasselbalch neutralization free energy penalty ΔGneutralization.

The integration of comprehensive diagnostic safeguards capable of automatically detecting biophysical anomalies, such as negative membrane resistivity states or non-converged stochastic correlation functions.
